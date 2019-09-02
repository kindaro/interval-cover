{-# language RecordWildCards
           , TypeFamilies
           , BlockArguments
           , TypeApplications
           , ScopedTypeVariables
  #-}

{-# options_ghc  -fdefer-typed-holes #-}

module Main where

import Prelude hiding ((^))
import qualified Prelude
import Control.Monad
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
import Data.Proxy

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
normalize u | Set.null u = Set.empty
            | otherwise = let  rel = closure (relation u joins)
                               classes = classifyBy (curry (rel ?)) u
                          in Set.map (bounds . flatten) classes

flatten :: Set I -> Set Int
flatten = let deconstruct (I x y) = Set.fromList [x, y] in Set.unions . Set.map deconstruct

bounds :: Set Int -> I
bounds xs = interval (Set.findMin xs) (Set.findMax xs)

data Relation a = Relation { table :: Matrix Binary, indices :: Map Int a }  -- Invariant: square.
    deriving Eq

instance Show a => Show (Relation a) where
    show = show . table

relation :: Ord a => Set a -> (a -> a -> Bool) -> Relation a
relation u f = Relation{..} where
        n = Set.size u
        table = matrix n n (\(i, j) -> fromBool $ (indices ! i) `f` (indices ! j))
        indices = Map.fromDistinctAscList $ zip [1..] (Set.toAscList u)

(?) :: Eq a => Relation a -> (a, a) -> Bool
Relation{..} ? (x, y) = let { [i] = inverseLookup indices x ; [j] = inverseLookup indices y }
                        in toBool $ Matrix.getElem i j table

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

data Binary = No | Yes deriving (Eq, Ord, Bounded, Enum)

fromBool True = Yes
fromBool False = No

toBool Yes = True
toBool No = False

instance Show Binary where
    show Yes = "#"
    show No  = "."

instance Num Binary where
    No  + Yes = Yes
    Yes + No  = Yes
    _   + _   = No
    Yes * Yes = Yes
    _   * _   = No
    negate = id
    abs = id
    signum = id
    fromInteger = fromBool . odd

(^) :: Binary -> Binary -> Binary
x ^ y = x + y + (x * y)

instance Arbitrary Binary where
    arbitrary = arbitraryBoundedEnum

reflexiveClosure :: Relation a -> Relation a
reflexiveClosure Relation{..} = Relation{ table = Matrix.elementwise (^) table d, ..}
    where d = Matrix.diagonalList (Map.size indices) No (repeat Yes)

symmetricClosure :: Relation a -> Relation a
symmetricClosure Relation{..} = Relation{ table = Matrix.elementwise (^) table t, ..}
    where t = Matrix.transpose table

transitiveClosure :: Relation a -> Relation a
transitiveClosure Relation{..} = Relation { table = f table, .. }
    where f = last . converge . scanl1 g . repeat
          g' x y = Matrix.elementwise (+) x (x `Matrix.multStd` y)
          g = throughInteger g'
          throughInteger :: (Matrix Integer -> Matrix Integer -> Matrix Integer)
                         -> Matrix Binary -> Matrix Binary -> Matrix Binary
          throughInteger f x y = fmap (toEnum . fromInteger . signum) $ f (fmap convert x) (fmap convert y)
          convert = (fromIntegral :: Int -> Integer) . fromEnum

closure :: Relation a -> Relation a
closure = transitiveClosure . symmetricClosure . reflexiveClosure

converge :: Eq a => [a] -> [a]
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
    arbitrary = do
        (Positive size) <- arbitrary @(Positive Float)
        spread <- scale (* 5) (arbitrary @Int)
        return $ interval (spread - floor (size / 2)) (spread + ceiling (size / 2))
    shrink (I 0 0) = [ ]
    shrink i = [resizeTo0 i]
        where nudge x = x - signum x
              resizeTo0 (I x y) | abs x >  abs y = interval (nudge x) y
                                | abs x == abs y = interval (nudge x) (nudge y)
                                | abs x <  abs y = interval x (nudge y)

interval x y | x > y     = I y x
             | otherwise = I x y

isWithin :: Int -> I -> Bool
x `isWithin` I{..} = left <= x && x <= right

isWithinOneOf :: Int -> Set I -> Bool
x `isWithinOneOf` s  = or . Set.map (x `isWithin`) $ s

countWithin :: Set I -> Int -> Int
countWithin s x = sum . fmap (fromEnum . (x `isWithin`)) . Set.toList $ s

displayIntervals :: Set I -> String
displayIntervals xs =
  let (I leftBound rightBound) = (bounds . flatten) xs
      displayOne (I x y) = replicate (x - leftBound) '.'
                        ++ replicate (y - x + 1) '#'
                        ++ replicate (rightBound - y) '.' ++ pure '\n'
  in concatMap displayOne xs

precedes, meets, overlaps, isFinishedBy, contains, starts :: I -> I -> Bool
i `precedes` j      =  right i < left j
i `meets` j         =  right i == left j
i `overlaps` j      =  left i < left j && right i < right j && right i > left j
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

main = defaultMain $ testGroup "Properties."
    [ testGroup "Relations."
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
        ]

    , testGroup "Intervals."
        [ testProperty "Shrinking intervals converges" \i ->
            List.elem [ ] . take 1000 . fmap ($ (i :: I)) . iterate (>=> List.nub . shrink) $ return
        ]

    , testGroup "Classification."
        [ testProperty "Union inverts classification" $
            displayingRelation \xs f rel ->
                let equivalence = closure rel
                    classes = classifyBy (curry (equivalence ?)) xs
                in  QuickCheck.classify (Set.size classes > 1) "Non-trivial equivalence" $
                        Set.unions classes == xs
        , testProperty "Intersection of a classification is empty" $
            displayingRelation \xs f rel -> if Set.null xs then property True else
                let equivalence = closure rel
                    classes = classifyBy (curry (equivalence ?)) xs
                in  QuickCheck.classify (Set.size classes > 1) "Non-trivial equivalence" $ property $
                        if Set.size classes == 1 then classes == Set.singleton xs else
                            foldr1 Set.intersection classes == Set.empty
        , testProperty "Belonging to the same class = equivalent by the defining relation" $
            displayingRelation \xs f rel -> if Set.null xs then property True else
                let equivalence = closure rel
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

    ,  testGroup "Normalizer."
        [ testProperty "Normal set of intervals is pairwise disjoint" \s ->
            let t = normalize s
            in QuickCheck.classify (s /= t) "Non-trivial normalization"
                . counterexample (displayIntervals s) . counterexample (displayIntervals t)
                $ if Set.size t < 2 then return True else do
                    x <- choose (0, Set.size t - 1)
                    let i = Set.elemAt x t
                        t' = Set.deleteAt x t
                    y <- choose (0, Set.size t' - 1)
                    let j = Set.elemAt y t'
                    return $ i `isDisjointWith` j
        , testProperty "Normalization is idempotent" \s ->
            QuickCheck.classify (normalize s /= s) "Non-trivial normalization"
            let t = normalize s
                t' = normalize t
            in  counterexample (displayIntervals s) . counterexample (displayIntervals t)
                . counterexample (displayIntervals t')
                $ t == t'
        , testProperty "Preserves pointwise coverage" $ \s x ->
            let t = normalize s
            in  QuickCheck.classify (countWithin s x == 1) "Point is within exactly once"
                . QuickCheck.classify (t /= s) "Non-trivial normalization"
                . QuickCheck.classify (countWithin s x > 1) "Point is within more than once"
                .  QuickCheck.classify (not $ x `isWithinOneOf` s) "Point is without"
                . counterexample (displayIntervals s) . counterexample (displayIntervals t)
                $ (countWithin s x >= 1) == (countWithin t x == 1)
        ]
    , checkCommutativeRingAxioms (Proxy @Binary) "Binary"
    ]

checkCommutativeRingAxioms :: forall a. (Eq a, Num a, Show a, Arbitrary a) => Proxy a -> String -> TestTree
checkCommutativeRingAxioms Proxy typeName = testGroup ("Ring axioms for " ++ typeName ++ ".")
    [ testProperty "Addition is associative" \x y z ->
        let _ = (x :: a) in (x + y) + z == x + (y + z)
    , testProperty "Addition is commutative" \x y ->
        let _ = (x :: a) in x + y == y + x
    , testProperty "Multiplication is associative" \x y z ->
        let _ = (x :: a) in (x * y) * z == x * (y * z)
    , testProperty "Multiplication is commutative" \x y ->
        let _ = (x :: a) in x * y == y * x
    , testProperty "Negation is compatible with zero" \x ->
        let _ = (x :: a) in (x + negate x) + x == x
    , testProperty "There is only one zero" \x y ->
        let _ = (x :: a) in x + negate x == y + negate y
    , testProperty "Left distribution" \x y z ->
        let _ = (x :: a) in x * (y + z) == (x * y) + (x * z)
    , testProperty "Right distribution" \x y z ->
        let _ = (x :: a) in (y + z) * x == (y * x) + (z * x)
    ]
