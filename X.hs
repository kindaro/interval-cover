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

data I = I { left, right :: Int }  -- Invariant: ordered.
    deriving (Eq, Ord, Show)

instance Arbitrary I where
    arbitrary = arbitrary >>= return . uncurry interval

interval x y | x > y     = I y x
             | otherwise = I x y

within :: Int -> I -> Bool
x `within` I{..} = left <= x && x <= right

precedes, meets, overlaps, isFinishedBy, contains, starts :: I -> I -> Bool
i `precedes` j      =  right i < left j
i `meets` j         =  right i == left j
i `overlaps` j      =  left i < left j && right i < right j
i `isFinishedBy` j  =  left i < left j && right i == right j
i `contains` j      =  left i < left j && right i > right j
i `starts` j        =  left i == left j && right i < right j

i `absorbs` j        = i `isFinishedBy` j || i `contains` j || j `starts` i
i `touches` j        = i `meets` j || i `overlaps` j
i `isDisjointWith` j = i `precedes` j || j `precedes` i
i `isRightwardsOf` j = j `precedes` i || j `touches` i

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
