{-# language RecordWildCards
           , TypeFamilies
           , BlockArguments
  #-}

{-# options_ghc  -fdefer-typed-holes #-}

module Main where

import Data.List.Ordered (union)
import Data.List (groupBy)
import Data.Function (on)
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
import Test.Tasty.QuickCheck hiding (classify)
import qualified Test.Tasty.QuickCheck as QuickCheck
import Test.Tasty
import Data.Function

inverseLookup :: Eq v => Map k v -> v -> [k]
inverseLookup m v = fmap snd . filter ((== v) . fst) . fmap swap . Map.assocs $ m

classify :: Ord a => Set a -> Set (Set a)
classify = classifyBy (==)

classifyBy :: Ord a => (a -> a -> Bool) -> Set a -> Set (Set a)
classifyBy eq = Set.fromList . Map.elems . List.foldl' f Map.empty . Set.toList
  where
    f m x = case List.find (`eq` x) (Map.keys m) of
        Just k  -> Map.insertWith Set.union k (Set.singleton x) m
        Nothing -> Map.insert x (Set.singleton x) m

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

instance Show a => Show (Relation a) where
    show = show . table

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

reflexiveClosure :: Relation a -> Relation a
reflexiveClosure Relation{..} = Relation{ table = Matrix.elementwise (||) table d, ..}
    where d = Matrix.diagonalList (Map.size indices) False (repeat True)

symmetricClosure :: Relation a -> Relation a
symmetricClosure Relation{..} = Relation{ table = Matrix.elementwise (||) table t, ..}
    where t = Matrix.transpose table

transitiveClosure :: Relation a -> Relation a
transitiveClosure Relation{..} = Relation { table = f table, .. }
    where f = last . converge . scanl1 g . repeat
          g x y = Matrix.elementwise (||) x (Matrix.multStd x y)

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

displayingRelation :: Testable prop => (Set Int -> (Int -> Int -> Bool) -> Relation Int -> prop) -> Property
displayingRelation p = forAllShrink arbitrary shrink \(Blind (MostlyNot f)) -> forAllShrink arbitrary shrink \xs ->
    let rel = relation xs f in counterexample (show rel) $ (p xs f rel)

oneOfSet :: (Testable prop, Show a, Arbitrary a) => Set a -> (a -> prop) -> Property
oneOfSet set = forAll ((oneof . fmap return . Set.toList) set)

newtype MostlyNot = MostlyNot (Int -> Int -> Bool)

instance Arbitrary MostlyNot where
    arbitrary = do
        f <- arbitrary
        return $ MostlyNot \x y -> if x * y `mod` 11 == 0 then f x y else False

main = defaultMain $ testGroup ""
    [ testProperty "The relation type is isomorphic to the original relation" $
        displayingRelation \xs f rel -> if null xs then property True else
            oneOfSet xs \x -> oneOfSet xs \y -> rel ? (x, y) ==  x `f` y
    , testProperty "A relation is not necessarily reflexive" $ expectFailure $
        displayingRelation \_ _ rel -> isReflexive rel
    , testProperty "Reflexive closure of a relation is reflexive" $
        displayingRelation \_ _ rel -> (isReflexive . reflexiveClosure) rel
    , testProperty "A relation is not necessarily symmetric" $ expectFailure $
        displayingRelation \_ _ rel -> isSymmetric rel
    , testProperty "Symmetric closure of a relation is symmetric" $
        displayingRelation \_ _ rel -> (isSymmetric . symmetricClosure) rel
    , testProperty "A relation is not necessarily transitive" $ expectFailure $
        displayingRelation \_ _ rel -> isTransitive rel
    , testProperty "Transitive closure of a relation is transitive" $
        displayingRelation \_ _ rel -> (isTransitive . transitiveClosure) rel
    , testProperty "Union inverts classification" $
        displayingRelation \xs f rel ->
            let equivalence = (transitiveClosure . symmetricClosure . reflexiveClosure) rel
                classes = classifyBy (curry (equivalence ?)) xs
            in  QuickCheck.classify (Set.size classes > 1) "Non-trivial equivalence" $
                    Set.unions classes == xs
    , testProperty "Intersection of a classification is empty" $
        displayingRelation \xs f rel -> if Set.null xs then property True else
            let equivalence = (transitiveClosure . symmetricClosure . reflexiveClosure) rel
                classes = classifyBy (curry (equivalence ?)) xs
            in  QuickCheck.classify (Set.size classes > 1) "Non-trivial equivalence" $ property $
                    if Set.size classes == 1 then classes == Set.singleton xs else
                        foldr1 Set.intersection classes == Set.empty
    , testProperty "Belonging to the same class = equivalent by the defining relation" $
        displayingRelation \xs f rel -> if Set.null xs then property True else
            let equivalence = (transitiveClosure . symmetricClosure . reflexiveClosure) rel
                classes = classifyBy (curry (equivalence ?)) xs
                (===) :: Int -> Int -> Bool
                (===) = (==) `on` \x -> Set.filter (x `Set.member`) classes
            in  QuickCheck.classify (Set.size classes > 1) "Non-trivial equivalence" $ property $
                    oneOfSet xs \x -> oneOfSet xs \y ->
                    counterexample (show $ Set.filter (x `Set.member`) classes) $
                    counterexample (show $ Set.filter (y `Set.member`) classes) $
                    counterexample (show equivalence) $
                        equivalence ? (x, y) == (x === y)
    , testProperty "Every element belongs to exactly one class" $
        displayingRelation \xs f rel -> if Set.null xs then property True else
            let equivalence = (transitiveClosure . symmetricClosure . reflexiveClosure) rel
                classes = classifyBy (curry (equivalence ?)) xs
            in  QuickCheck.classify (Set.size classes > 1) "Non-trivial equivalence" $ property $
                    counterexample (show classes) $ counterexample (show equivalence) $
                        length (Set.unions classes) == (sum . fmap length . Set.toList) classes
    ]
