{-# language RecordWildCards
           , TypeFamilies
           , BlockArguments
           , TypeApplications
           , ScopedTypeVariables
           , DeriveGeneric
           , FlexibleInstances
  #-}

{-# options_ghc  -fdefer-typed-holes #-}

module Main where

import Control.Monad
import Data.List.Ordered (union)
import Data.List (groupBy)
import Data.Function (on)
import Data.Foldable (null, toList)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Matrix (Matrix, matrix)
import qualified Data.Matrix as Matrix
import qualified Data.List as List
import Data.Tuple (swap)
import Test.Tasty.QuickCheck hiding (classify)
import Test.Tasty.HUnit
import qualified Test.Tasty.QuickCheck as QuickCheck
import Test.Tasty
import Data.Function
import Data.Proxy
import Control.DeepSeq
import GHC.Generics (Generic)

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

normalizeList :: [I] -> [I]
normalizeList = Set.toList . normalize . Set.fromList

flatten :: Set I -> Set Int
flatten = let deconstruct (I x y) = Set.fromList [x, y]
              deconstruct (P x) = Set.singleton x
          in Set.unions . Set.map deconstruct

bounds :: Set Int -> I
bounds xs = interval (Set.findMin xs) (Set.findMax xs)

data Relation a = Relation { table :: Matrix Binary, indices :: Map Int a }  -- Invariant: square.
    deriving Eq

instance Show a => Show (Relation a) where
    show = show . table

blank :: Ord a => Set a -> Relation a
blank set = relation set ((const.const) False)

complete :: Ord a => Set a -> Relation a
complete set = relation set ((const.const) True)

equality :: Ord a => Set a -> Relation a
equality set = (blank set) { table = Matrix.diagonalList (Set.size set) No (repeat Yes) }

elementwise :: Eq a => (Binary -> Binary -> Binary) -> Relation a -> Relation a -> Relation a
elementwise f u v
    | indices u /= indices v = error "Elementwise only works on relations over the same set."
    | otherwise = Relation { table = Matrix.elementwise f (table u) (table v), indices = indices u }

relation :: Ord a => Set a -> (a -> a -> Bool) -> Relation a
relation u f = Relation{..} where
        n = Set.size u
        table = matrix n n (\(i, j) -> fromBool $ (indices ! i) `f` (indices ! j))
        indices = Map.fromDistinctAscList $ zip [1..] (Set.toAscList u)

(?) :: Eq a => Relation a -> (a, a) -> Bool
Relation{..} ? (x, y) = let { [i] = inverseLookup indices x ; [j] = inverseLookup indices y }
                        in toBool $ Matrix.getElem i j table

isEmpty = null . indices

randomIndex :: Relation a -> Gen a
randomIndex = oneof . fmap return . Map.elems . indices

isReflexive, isSymmetric, isTransitive :: (Eq a, Show a) => Relation a -> Property

isReflexive r = if isEmpty r then property True else
    forAll (randomIndex r) \x ->
    r ? (x, x) == True

isSymmetric r = if isEmpty r then property True else
    forAll (randomIndex r) \x ->
    forAll (randomIndex r) \y ->
    r ? (x, y) == r ? (y, x)

isTransitive r = if isEmpty r then property True else
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

instance Arbitrary Binary where
    arbitrary = arbitraryBoundedEnum

reflexiveClosure :: Relation a -> Relation a
reflexiveClosure Relation{..} = Relation{ table = Matrix.elementwise (+*) table d, ..}
    where d = Matrix.diagonalList (Map.size indices) No (repeat Yes)

symmetricClosure :: Relation a -> Relation a
symmetricClosure Relation{..} = Relation{ table = Matrix.elementwise (+*) table t, ..}
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

data I = I Int Int  -- Invariant: ordered.
       | P Int
    deriving (Eq, Ord, Show, Generic)

instance NFData I

instance Arbitrary I where
    arbitrary = do
        (NonZero size) <- arbitrary @(NonZero Float)
        spread <- scale (* 5) (arbitrary @Int)
        return $ interval (spread - floor (size / 2)) (spread + floor (size / 2))
    shrink (P 0) = [ ]
    shrink (I 0 0) = [ ]
    shrink i = resizeTo0 i
      where
        nudge x = x - signum x
        resizeTo0 (I x y)
            | abs x >  abs y = [ interval (nudge x) y ]
            | abs x <  abs y = [ interval x (nudge y) ]
            | abs x == abs y = [ interval x (nudge y)
                               , interval (nudge x) y
                               , interval (nudge x) (nudge y) ]
        resizeTo0 (P x)                    = [ point (nudge x) ]

interval x y | x == y   = P x
             | x <  y   = I x y
             | x >  y   = I y x

(~~) = interval

point = P

left, right :: I -> Int
left  (I x _) = x
left  (P x)   = x
right (I _ y) = y
right (P y)   = y

isWithin :: Int -> I -> Bool
y `isWithin` (I x z) = x <= y && y <= z
y `isWithin` (P x) = x == y

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
      displayOne (P x) = replicate (x - leftBound) '.'
                      ++ "#"
                      ++ replicate (rightBound - x) '.' ++ pure '\n'
  in concatMap displayOne xs

instance Num (I -> I -> Bool) where
    p + q = \i j -> i `p` j /= i `q` j
    p * q = \i j -> i `p` j && i `q` j
    negate = id
    abs = id
    signum = id
    fromInteger = error "`fromInteger` is not defined for binary conditionals."

instance CoArbitrary I

instance Show (I -> I -> Bool) where
    show p = let xs = Set.fromList [ interval i (i + 3) | i <- [1, 3.. 7] ]
             in show (relation xs p)

instance Eq (I -> I -> Bool) where
    p == q = let xs = Set.fromList [ interval i (i + 3) | i <- [1, 3.. 7] ]
             in relation xs p == relation xs q

(+*) :: Num a => a -> a -> a
x +* y = x + y + (x * y)

precedes, meets, overlaps, isFinishedBy, contains, starts :: I -> I -> Bool
precedes =     \ i j  ->  right i < left j
meets =        \ i j  ->  right i == left j && left i /= left j && right i /= right j
overlaps =     \ i j  ->  left i < left j  && right i < right j  && right i > left j
isFinishedBy = \ i j  ->  left i < left j  && right i == right j
contains =     \ i j  ->  left i < left j  && right i > right j
starts =       \ i j  ->  left i == left j && right i < right j

absorbs = isFinishedBy +* contains +* flip starts +* (==)
isDisjointWith = precedes +* flip precedes
touches = meets +* overlaps
joins = (fmap . fmap) not isDisjointWith
isRightwardsOf = flip (precedes +* touches)

subsume :: Set I -> I -> Bool
xs `subsume` x = any (`absorbs` x) (normalize xs)

coveringChains :: I -> [I] -> [[I]]
coveringChains x ys = base ++ recursive
  where
    base = do
        y <- ys
        if y `absorbs` x then return (pure y) else fail ""

    recursive = do
        z <- filter (`overlaps` x) ys
        zs <- coveringChains (interval (right z) (right x)) (filter (`isRightwardsOf` z) ys)
        return $ z: zs

coveringMinimalChains x = List.nub . fmap minimizeChain . coveringChains x

minimizeChain :: [I] -> [I]
minimizeChain xs = last . converge $ ys
    where ys = iterate (join . flip cutTransitivitiesList touches) xs

transitivities :: Ord a => Set a -> (a -> a -> Bool) -> Set a
transitivities set (?) =
  let xs = Set.toList set
  in Set.fromList [ y | x <- xs, y <- xs, z <- xs, x ? y, x ? z, y ? z ]

cutTransitivitiesList :: Ord a => [a] -> (a -> a -> Bool) -> [[a]]
cutTransitivitiesList set rel = Set.toList . Set.map Set.toList
                              $ cutTransitivities (Set.fromList set) rel

cutTransitivities :: Ord a => Set a -> (a -> a -> Bool) -> Set (Set a)
cutTransitivities set rel =
  let t = transitivities set rel
  in if Set.null t then Set.singleton set else Set.map (`Set.delete` set) t

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
    [ testGroup "Cases."
        [ testGroup "Relations."
            [ testCaseSteps "`absorbs`" \step -> do
                assertBool "" $ interval 1 4 `absorbs` point 1
                assertBool "" $ interval 1 4 `absorbs` interval 1 3
                assertBool "" $ interval 1 4 `absorbs` interval 1 4
                assertBool "" $ interval 1 4 `absorbs` interval 2 3
                assertBool "" $ interval 1 4 `absorbs` interval 2 4
                assertBool "" $ interval 1 4 `absorbs` point 4
            , testCaseSteps "not `absorbs`" \step -> do
                assertBool "" . not $ interval 1 4 `absorbs` point 0
                assertBool "" . not $ interval 1 4 `absorbs` interval 0 1
                assertBool "" . not $ interval 1 4 `absorbs` interval 0 2
                assertBool "" . not $ interval 1 4 `absorbs` interval 0 4
                assertBool "" . not $ interval 1 4 `absorbs` interval 1 5
                assertBool "" . not $ interval 1 4 `absorbs` interval 2 5
                assertBool "" . not $ interval 1 4 `absorbs` interval 4 5
                assertBool "" . not $ interval 1 4 `absorbs` point 5
            , testCaseSteps "`isRightwardsOf`" \step -> do
                assertBool "" $ interval 2 4 `isRightwardsOf` interval 1 3
            , testCaseSteps "not `isRightwardsOf`" \step -> do
                assertBool "" . not $ interval 2 4 `isRightwardsOf` interval 1 5
                assertBool "" . not $ interval 2 4 `isRightwardsOf` interval 2 5
                assertBool "" . not $ interval 2 4 `isRightwardsOf` interval 3 5
                assertBool "" . not $ interval 2 4 `isRightwardsOf` interval 4 5
        ]
        , testGroup "Chains."
            [ testCase "Simple covering chains"
                $ coveringMinimalChains
                    (interval 1 3) [interval 0 3, interval 0 4, interval 1 3, interval 1 4]
                        @?= [[interval 0 3], [interval 0 4], [interval 1 3], [interval 1 4]]
            , testCaseSteps "Non-covering interval set" \step -> do
                coveringMinimalChains
                    (interval 2 4)
                        [ interval 0 2, point 1, interval 1 2, interval 1 3
                        , point 2, interval 2 3
                        ]
                        @?= [ ]
                coveringMinimalChains
                    (interval 2 4)
                        [ point 3, interval 3 4, interval 3 5
                        , point 4, interval 4 5
                        ]
                        @?= [ ]
                coveringMinimalChains
                    (interval 2 5)
                        [ interval 0 2, point 1, interval 1 2, interval 1 3
                        , point 2, interval 2 3
                        , point 3
                        , point 4, interval 4 5, interval 4 6
                        , point 5, interval 5 6
                        ]
                        @?= [ ]
            , testCase "A set with extra intervals and point join"
                $ coveringMinimalChains
                    (interval 2 5)
                    [interval 1 3, interval 2 4, interval 3 6]
                        @?= [ [interval 1 3, interval 3 6] ]
            , testCase "A set with extra intervals and extended join"
                $ coveringMinimalChains
                    (interval 2 7)
                    [interval 1 4, interval 2 5, interval 3 7]
                        @?= [ [interval 1 4, interval 3 7] ]
            ]
        ]

    , testGroup "Relations."
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
            within (10 ^ 4) . withMaxSuccess 1000
            $ let nubShrink = fmap List.nub . (>=> shrink)
              in List.elem [ ] . take 1000 . fmap ($ (i :: I)) . iterate nubShrink $ return
        ]

    , testGroup "Relations on intervals."
        let core = [ precedes, meets, overlaps, isFinishedBy, contains, starts ]
            basic = core ++ fmap flip core ++ [(==)]
        in
            [ testProperty "Exhaustive" \intervals ->
                let rels = fmap (relation intervals) basic
                in List.foldl1' (elementwise (+*)) rels == complete intervals
            , testProperty "Pairwise distinct" \intervals ->
                let rels = fmap (relation intervals) basic
                in QuickCheck.withMaxSuccess 1000 do
                    (s, t) <- anyTwo rels
                    return
                        $ counterexample (show s) . counterexample (show t) $ elementwise (*) s t == blank intervals
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
                    (i, j) <- anyTwo t
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
    , checkCommutativeRingAxioms (Proxy @(I -> I -> Bool)) "I -> I -> Bool"

    , testGroup "Chains."
        [ testProperty "A chain terminates" \base intervals ->
            let chains = coveringChains base intervals
            in within (10 ^ 4) . withMaxSuccess 1000
                $ chains `deepseq` True
        , testProperty "A normalized chain is a singleton" \base intervals ->
            let normalChains = fmap normalizeList (coveringChains base intervals)
            in counterexample (show normalChains)
                $ and . fmap ((1 ==) . length) $ normalChains
        , testProperty "A chain is a cover" \base intervals ->
            let chains = Set.fromList . fmap (normalize . Set.fromList) $ coveringChains base intervals
            in and . Set.map (`subsume` base) $ chains
        , testProperty "A chain is not necessarily minimal" \base intervals ->
            let chains = coveringChains base intervals
                subchains = List.nub (chains >>= dropOne)
            in expectFailure . within (10 ^ 6) $ (or . fmap ((`subsume` base) . Set.fromList)
                $ fmap normalizeList subchains) == False
        , testProperty "A minimized chain is minimal" \base intervals ->
            let chains = coveringMinimalChains base intervals
                subchains = List.nub (chains >>= dropOne)
            in within (10 ^ 6) $ (or . fmap ((`subsume` base) . Set.fromList)
                $ fmap normalizeList subchains) == False
        ]
    ]

dropOne :: [a] -> [[a]]
dropOne [ ] = [ ]
dropOne xs = do
               index <- [0.. length xs - 1]
               let ys = deleteAt index xs
               return ys

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

deleteAt :: Int -> [a] -> [a]
deleteAt idx xs = lft ++ rgt
  where (lft, (_:rgt)) = splitAt idx xs

anyTwo :: (Show (f a), Foldable f) => f a -> Gen (a, a)
anyTwo set
    | length set > 1 = do
        let list = toList set
        x <- choose (0, length list - 1)
        let s = list !! x
            list' = deleteAt x list
        y <- choose (0, length list' - 1)
        let t = list' !! y
        return (s, t)
    | otherwise = error $ "anyTwo cannot find two distinct elements: \
                            \set " ++ show set ++ " is too small."
