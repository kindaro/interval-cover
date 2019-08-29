{-# language RecordWildCards
           , TypeFamilies
  #-}

module X where

import Data.List.Ordered (union)
import Data.List (groupBy)
import Data.Function (on)
import Test.QuickCheck
import GHC.Exts
import Data.Foldable (null)

data I = I { left, right :: Int }  -- Invariant: strictly ordered.
    deriving (Eq, Ord, Show)

instance Arbitrary I where
    arbitrary = arbitrary >>= return . uncurry interval

interval x y | x > y     = I y x
             | otherwise = I x y

within :: Int -> I -> Bool
x `within` I{..} = left <= x && x <= right

unsafeUnion :: X -> X -> X
unsafeUnion (X xs) (X ys) = X (xs `union` ys)

precedes, meets, overlaps, isFinishedBy, contains, starts :: I -> I -> Bool
i `precedes` j      =  right i < left j
i `meets` j         =  right i == left j
i `overlaps` j      =  left i < left j && right i < right j
i `isFinishedBy` j  =  left i < left j && right i == right j
i `contains` j      =  left i < left j && right i > right j
i `starts` j        =  left i == left j && right i < right j

i `absorbs` j = i `isFinishedBy` j || i `contains` j || j `starts` i
i `touches` j = i `meets` j || i `overlaps` j
i `isDisjointWith` j = i `precedes` j || j `precedes` i

newtype X = X { xs :: [I] }  -- Invariant: sorted disjoint union of intervals.
    deriving (Eq, Show)

singleton x = X [x]

instance Semigroup X where
    (X [ ]) <> v = v
    u <> (X [ ]) = u
    u@(X (x: xs)) <> v@(X (y: ys))
        | x `precedes` y = unsafeUnion (X [x]) (X xs <> v)
        | y `precedes` x = unsafeUnion (X [y]) (X ys <> u)
        | x `touches` y = unsafeUnion (X [I (left x) (right y)]) (X xs <> X ys)
        | y `touches` x = unsafeUnion (X [I (left y) (right x)]) (X ys <> X xs)
        | x `absorbs` y = unsafeUnion (X [x]) (X xs <> X ys)
        | y `absorbs` x = unsafeUnion (X [y]) (X xs <> X ys)

instance Monoid X where
    mempty = X mempty

instance IsList X where
    type Item X = I
    fromList = foldr (\x u -> singleton x <> u) mempty
    toList = xs

debugFromList = scanr (\x u -> singleton x <> u) mempty

x `isRightwardsOf` y = y `precedes` x || y `touches` x

chains :: I -> [I] -> [[I]]
chains x ys = base ++ recursive
  where
    base = do
        y <- ys
        if y `absorbs` x then return (pure y) else fail ""

    recursive = do
        z <- filter (`touches` x) ys
        zs <- chains (interval (right z) (right x)) (filter (`isRightwardsOf` z) ys)
        return $ z: zs
