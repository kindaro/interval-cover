{-# language RecordWildCards
           , TypeFamilies
  #-}

{-# options_ghc  -fdefer-typed-holes #-}

module X where

import Data.List.Ordered (union)
import Data.List (groupBy)
import Data.Function (on)
import Test.QuickCheck
import GHC.Exts
import Data.Foldable (null)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Matrix (Matrix, matrix)
import qualified Data.Matrix as Matrix
import qualified Data.List as List
import Data.Tuple (swap)

inverseLookup :: Eq v => Map k v -> v -> [k]
inverseLookup m v = fmap snd . filter ((== v) . fst) . fmap swap . Map.assocs $ m

e1 = Set.fromList [ interval x (x + 2) | x <- [1..10] ]
e2 = Set.fromList [ interval 1 3, interval 2 4, interval 5 7 ]

normalize :: Set I -> Set I
normalize u = _z
-- -- 1. Transitive closure will help me. I must form the transitive closure of the `joins` relation
-- -- which is already symmetric and reflexive. This will turn said relation into equivalence.
-- -- 2. I can then divide the intervals into equivalence classes and simply take the left of the
-- -- smallest and the right of the largest.
-- --
-- -- But I cannot consider transitive closure of a relation by itself --- it is not finite. I should
-- -- rather consider it with regard to the set at hand.

data Relation a = Relation { table :: Matrix Bool, indices :: Map Int a }  -- Invariant: square.

relation :: Ord a => Set a -> (a -> a -> Bool) -> Relation a
relation u f = Relation{..} where
        n = Set.size u
        table = matrix n n (\(i, j) -> (indices ! i) `f` (indices ! j))
        indices = Map.fromDistinctAscList $ zip [1..] (Set.toAscList u)

(?) :: Eq a => Relation a -> (a, a) -> Bool
Relation{..} ? (x, y) = let { [i] = inverseLookup indices x ; [j] = inverseLookup indices y }
                        in Matrix.getElem i j table

-- Check: ? on a relation is the same as the original operation.

empty = null . indices

randomIndex :: Relation a -> Gen a
randomIndex = oneof . fmap return . Map.elems . indices

isReflexive, isSymmetric, isTransitive :: (Eq a, Show a) => Relation a -> Property

isReflexive r = if empty r then property True else
    forAll (randomIndex r) \x ->
    r ? (x, x) == True

isSymmetric r = if empty r then property True else
    forAll (randomIndex r) \x ->
    forAll (randomIndex r) \y ->
    r ? (x, y) == r ? (y, x)

isTransitive r = if empty r then property True else
    forAll (randomIndex r) \x ->
    forAll (randomIndex r) \y ->
    forAll (randomIndex r) \z ->
    r ? (x, y) && r ? (y, z) ==> r ? (x, z)

instance Num Bool where
    (+) = (||)
    (*) = (&&)
    negate = id
    abs = id
    signum = id
    fromInteger = odd

closure :: Relation a -> Relation a
closure Relation{..} = let f = last . converge . scanl1 Matrix.multStd . repeat
                       in Relation { table = f table, .. }

converge = convergeBy (==)

convergeBy :: (a -> a -> Bool) -> [a] -> [a]
convergeBy _ [ ] = [ ]
convergeBy _ [x] = [x]
convergeBy eq (x: xs@(y: _))
    | x `eq` y = [x]
    | otherwise = x : convergeBy eq xs

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
i `joins` j          = not (i `isDisjointWith` j)
i `isRightwardsOf` j = j `precedes` i || j `touches` i

subsume :: Set I -> I -> Bool
xs `subsume` x = any (`absorbs` x) (normalize xs)

coveringChains :: I -> [I] -> [[I]]
coveringChains x ys = base ++ recursive
  where
    base = do
        y <- ys
        if y `absorbs` x then return (pure y) else fail ""

    recursive = do
        z <- filter (`touches` x) ys
        zs <- coveringChains (interval (right z) (right x)) (filter (`isRightwardsOf` z) ys)
        return $ z: zs

-- λ traverse_ print $ coveringChains (interval 2 5) [interval 1 3, interval 2 4, interval 3 5, interval 4 6]
-- [I {left = 1, right = 3},I {left = 2, right = 4},I {left = 3, right = 5}]
-- [I {left = 1, right = 3},I {left = 2, right = 4},I {left = 4, right = 6}]

-- Definition of a covering chain:
-- 1. Sufficient: Subsumes the given interval.
-- 2. Minimal: If any element is removed, does not subsume anymore.
