{-# language RecordWildCards
           , TypeFamilies
           , BlockArguments
           , TypeApplications
           , ScopedTypeVariables
           , DeriveGeneric
           , FlexibleInstances
           , FlexibleContexts
  #-}

{-# options_ghc  -fdefer-typed-holes #-}

module Main where

import Control.Monad
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
import Data.Proxy
import Control.DeepSeq
import GHC.Generics (Generic)

import Willem

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

normalize :: Ord a => Set (Interval a) -> Set (Interval a)
normalize u | Set.null u = Set.empty
            | otherwise = let  rel = closure (relation u joins)
                               classes = classifyBy (curry (rel ?)) u
                          in Set.map (bounds . flatten) classes

normalizeList :: Ord a => [Interval a] -> [Interval a]
normalizeList = Set.toList . normalize . Set.fromList

flatten :: Ord a => Set (Interval a) -> Set a
flatten = let deconstruct (Interval x y) = Set.fromList [x, y]
              deconstruct (Point x) = Set.singleton x
          in Set.unions . Set.map deconstruct

bounds :: Ord a => Set a -> Interval a
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

isEmpty :: Relation a -> Bool
isEmpty = null . indices

randomIndex :: Relation a -> Gen a
randomIndex = oneof . fmap return . Map.elems . indices

isReflexive, isSymmetric, isAntisymmetric, isTransitive :: (Eq a, Show a) => Relation a -> Property

isReflexive r = if isEmpty r then property True else
    forAll (randomIndex r) \x ->
    r ? (x, x) == True

isSymmetric r = if isEmpty r then property True else
    forAll (randomIndex r) \x ->
    forAll (randomIndex r) \y ->
    r ? (x, y) == r ? (y, x)

isAntisymmetric r = if isEmpty r then property True else
    forAll (randomIndex r) \x ->
    forAll (randomIndex r) \y ->
    r ? (x, y) /= r ? (y, x)

isTransitive r = if isEmpty r then property True else
    forAll (randomIndex r) \x ->
    forAll (randomIndex r) \y ->
    forAll (randomIndex r) \z ->
    r ? (x, y) && r ? (y, z) ==> r ? (x, z)

data Binary = No | Yes deriving (Eq, Ord, Bounded, Enum)

fromBool :: Bool -> Binary
fromBool True = Yes
fromBool False = No

toBool :: Binary -> Bool
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
          throughInteger h x y = fmap (toEnum . fromInteger . signum) $ h (fmap convert x) (fmap convert y)
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

data Interval a = Interval a a  -- Invariant: ordered.
                | Point a
    deriving (Eq, Ord, Show, Generic)

instance NFData a => NFData (Interval a)

instance Arbitrary (Interval Int) where
    arbitrary = do
        x <- arbitrary @(Interval Float)
        return case x of
            Point y -> Point (floor y)
            Interval y z -> interval (floor y) (floor z)

instance {-# overlappable #-} (Arbitrary a, Fractional a, Ord a) => Arbitrary (Interval a) where
    arbitrary = do
        d6 <- fmap (`mod` 6) (arbitrary @Int)
        if d6 == 0
            then do
                spread <- scale (* 5) arbitrary
                return $ point (spread + 100)
            else do
                size <- arbitrary
                spread <- scale (* 5) arbitrary
                return $ interval (spread - size / 2) (spread + size / 2 + 100)
    shrink (Point 0) = [ ]
    shrink (Interval 0 0) = [ ]
    shrink i = resizeTo0 i
      where
        nudge x | abs x < abs (signum x)  =  0
                | otherwise  =  x - signum x
        resizeTo0 (Interval x y)
            | abs x >  abs y = [ interval (nudge x) y ]
            | abs x <  abs y = [ interval x (nudge y) ]
            | abs x == abs y = [ interval x (nudge y)
                               , interval (nudge x) y
                               , interval (nudge x) (nudge y) ]
            | otherwise = error "resizeTo0: Error: Interval is a pair without relation!"
        resizeTo0 (Point x)                    = [ point (nudge x) ]

interval :: Ord a => a -> a -> Interval a
interval x y | x == y   = Point x
             | x <  y   = Interval x y
             | x >  y   = Interval y x
             | otherwise = error "interval: Error: Order on the underlying type is not total!"

(~~) :: Ord a => a -> a -> Interval a
(~~) = interval

point :: Ord a => a -> Interval a
point = Point

left, right :: Interval a -> a
left  (Interval x _) = x
left  (Point x)   = x
right (Interval _ y) = y
right (Point y)   = y

isWithin :: Ord a => a -> Interval a -> Bool
y `isWithin` (Interval x z) = x <= y && y <= z
y `isWithin` (Point x) = x == y

isWithinOneOf :: Ord a => a -> Set (Interval a) -> Bool
x `isWithinOneOf` s  = or . Set.map (x `isWithin`) $ s

countWithin :: Ord a => Set (Interval a) -> a -> Int
countWithin s x = sum . fmap (fromEnum . (x `isWithin`)) . Set.toList $ s

displayIntervals :: forall a. (RealFrac a, Eq a)
                 => Set (Interval a) -> String
displayIntervals xs =
  let (Interval leftBound rightBound) = (bounds . flatten) xs
      leftBound'  = floor leftBound
      rightBound' = floor rightBound

      displayOne :: Interval a -> String
      displayOne (Interval x y) =
        let x' = floor x
            y' = floor y
        in replicate (x' - leftBound') '.'
            ++ (if x' == y' then "*" else "*" ++ replicate (y' - x' - 1) '-' ++ "*")
            ++ replicate (rightBound' - y') '.' ++ pure '\n'
      displayOne (Point x) =
        let x' = floor x
        in replicate (x' - leftBound') '.'
                      ++ "*"
                      ++ replicate (rightBound' - x') '.' ++ pure '\n'
  in concatMap displayOne xs

instance Num Bool where
    (+) = (/=)
    (*) = (&&)
    negate = id
    abs = id
    signum = id
    fromInteger = toEnum . fromInteger


-- instance {-# overlappable #-} Num (Interval a -> Bool) where
--     p + q = \i -> p i /= q i
--     p * q = \i -> p i && q i
--     negate = id
--     abs = id
--     signum = id
--     fromInteger = error "`fromInteger` is not defined for the ring of functions."

instance Num b => Num (Interval a -> b) where
    p + q = \i -> p i + q i
    p * q = \i -> p i * q i
    negate = id
    abs = id
    signum = id
    fromInteger = error "`fromInteger` is not defined for the ring of functions."

instance CoArbitrary a => CoArbitrary (Interval a)

instance (Show a, Ord a, Num a, Enum a) => Show (Interval a -> Interval a -> Bool) where
    show p = let xs = Set.fromList [ interval i (i + 3) | i <- [1, 3.. 7] ]
             in show (relation xs p)

instance (Ord a, Num a, Enum a) => Eq (Interval a -> Interval a -> Bool) where
    p == q = let xs = Set.fromList [ interval i (i + 3) | i <- [1, 3.. 7] ]
             in relation xs p == relation xs q

infixl 8 +*
(+*) :: Num a => a -> a -> a
x +* y = x + y + (x * y)

precedes, meets, overlaps, isFinishedBy, contains, starts
    :: Ord a => Interval a -> Interval a -> Bool
precedes      =  \ i j  ->  right i < left j
meets         =  \ i j  ->  right i == left j && left i /= left j && right i /= right j
overlaps      =  \ i j  ->  left i < left j  && right i < right j  && right i > left j
isFinishedBy  =  \ i j  ->  left i < left j  && right i == right j
contains      =  \ i j  ->  left i < left j  && right i > right j
starts        =  \ i j  ->  left i == left j && right i < right j

absorbs, isDisjointWith, joins, touches, isRightwardsOf
    :: Ord a => Interval a -> Interval a -> Bool
absorbs = isFinishedBy +* contains +* flip starts +* (==)
isDisjointWith = precedes +* flip precedes
joins = (fmap . fmap) not isDisjointWith
touches = meets +* overlaps
isRightwardsOf = flip (precedes +* touches)

subsume :: Ord a => Set (Interval a) -> Interval a -> Bool
xs `subsume` x = any (`absorbs` x) (normalize xs)

coveringChains :: forall a. (Ord a, Num a)
               => Interval a -> [Interval a] -> [[Interval a]]
coveringChains x ys = coveringChains' x ys initialLimit
  where
    initialLimit = interval ((\z -> z - 1) . left . bounds . flatten . Set.fromList $ ys) (left x)

coveringChains' :: forall a. (Ord a, Num a)
                => Interval a -> [Interval a] -> Interval a -> [[Interval a]]
coveringChains' x ys limit = base ++ recursive 
  where
    base :: [[Interval a]]
    base = do
        y <- filter (limit `touches`) ys
        if y `absorbs` x then return (pure y) else fail ""

    recursive :: [[Interval a]]
    recursive = do
        y <- filter (\y -> y `overlaps` x && limit `touches` y) ys
        zs <- coveringChains' @a
                (interval @a (right y) (right x))
                ((filter (`isRightwardsOf` y)) ys)
                (interval @a (right limit) (right y))
        return $ y: zs

coveringMinimalChains :: forall a. (Ord a, Num a)
               => Interval a -> [Interval a] -> [[Interval a]]
coveringMinimalChains x = List.nub . fmap minimizeChain . coveringChains x

chainsFromTo :: Ord a => Interval a -> Interval a -> [Interval a] -> [[Interval a]]
chainsFromTo start end xs' = base ++ recursive
  where
    xs = filter (not . isDisjointWith (interval (right start) (left end))) xs'

    base = do
        x <- filter ((start `touches`) +* (`touches` end)) xs
        return [x]

    recursive = do
        z <- filter ((start `touches`)) xs
        let xs' = filter (`isRightwardsOf` z) xs
        let start' = interval (right start) (right z)
        zs <- chainsFromTo start' end xs'

        return $ z: zs

coveringChainsFromTo :: forall a. (Ord a, Num a)
                     => Interval a -> [Interval a] -> [[Interval a]]
coveringChainsFromTo base xs = chainsFromTo start end xs
  where
    start = interval ((\z -> z - 1) . left $ boundsOfXs) (left base)
    end = interval (right base) ((\z -> z + 1) . right $ boundsOfXs)
    boundsOfXs = (bounds . flatten . Set.fromList) xs

isCovering :: Ord a => Interval a -> [Interval a] -> Bool
isCovering base xs = case (Set.toList . normalize . Set.fromList) xs of
                        [y] -> y `absorbs` base
                        _   -> False

isMinimalCovering :: Ord a => Interval a -> [Interval a] -> Bool
isMinimalCovering base xs = sufficient && minimal
    where sufficient = isCovering base xs
          minimal    = List.null . filter (isCovering base)
                                 . fmap (`deleteAt` xs) $ [0.. length xs - 1]

bruteForceCoveringChains :: forall a. (Ord a, Num a)
                         => Interval a -> [Interval a] -> [[Interval a]]
bruteForceCoveringChains base xs = filter (isMinimalCovering base) (List.subsequences xs)

minimizeChain :: (Eq a, Ord a) => [Interval a] -> [Interval a]
minimizeChain xs = last . converge $ ys
    where ys = iterate (join . flip cutTransitivitiesList touches) xs

transitivities :: Ord a => Set a -> (a -> a -> Bool) -> Set a
transitivities set eq =
  let xs = Set.toList set
  in Set.fromList [ y | x <- xs, y <- xs, z <- xs, x `eq` y, x `eq` z, y `eq` z ]

cutTransitivitiesList :: Ord a => [a] -> (a -> a -> Bool) -> [[a]]
cutTransitivitiesList set rel = Set.toList . Set.map Set.toList
                              $ cutTransitivities (Set.fromList set) rel

cutTransitivities :: Ord a => Set a -> (a -> a -> Bool) -> Set (Set a)
cutTransitivities set rel =
  let t = transitivities set rel
  in if Set.null t then Set.singleton set else Set.map (`Set.delete` set) t

-- λ traverse_ print $ coveringChains (interval 2 5) [interval 1 3, interval 2 4, interval 3 5, interval 4 6]
-- [Interval {left = 1, right = 3},Interval {left = 2, right = 4},Interval {left = 3, right = 5}]
-- [Interval {left = 1, right = 3},Interval {left = 2, right = 4},Interval {left = 4, right = 6}]

-- Definition of a covering chain:
-- 1. Sufficient: Subsumes the given interval.
-- 2. Minimal: If any element is removed, does not subsume anymore.

displayingRelation :: (Ord a, Show a, Arbitrary a, CoArbitrary a, Testable prop)
                   => (Set a -> (a -> a -> Bool) -> Relation a -> prop) -> Property
displayingRelation p = forAllShrink arbitrary shrink \(Blind (MostlyNot f)) -> forAllShrink arbitrary shrink \xs ->
    let rel = relation xs f in counterexample (show rel) $ (p xs f rel)

oneOfSet :: (Testable prop, Show a, Arbitrary a) => Set a -> (a -> prop) -> Property
oneOfSet set = forAll ((oneof . fmap return . Set.toList) set)

newtype MostlyNot a = MostlyNot (a -> a -> Bool)

instance (Arbitrary a, CoArbitrary a) => Arbitrary (MostlyNot a) where
    arbitrary = do
        f <- arbitrary
        d6 <- fmap (`mod` 6) (arbitrary @Int)
        return $ MostlyNot \x y -> if d6 == 0 then f x y else False

main :: IO ()
main = defaultMain $ testGroup "Properties."
    [ testGroup "Cases."
        [ testGroup "Relations."
            [ testCaseSteps "`absorbs`" \_ -> do
                assertBool "" $ interval @Int 1 4 `absorbs` point 1
                assertBool "" $ interval @Int 1 4 `absorbs` interval 1 3
                assertBool "" $ interval @Int 1 4 `absorbs` interval 1 4
                assertBool "" $ interval @Int 1 4 `absorbs` interval 2 3
                assertBool "" $ interval @Int 1 4 `absorbs` interval 2 4
                assertBool "" $ interval @Int 1 4 `absorbs` point 4
            , testCaseSteps "not `absorbs`" \_ -> do
                assertBool "" . not $ interval @Int 1 4 `absorbs` point 0
                assertBool "" . not $ interval @Int 1 4 `absorbs` interval 0 1
                assertBool "" . not $ interval @Int 1 4 `absorbs` interval 0 2
                assertBool "" . not $ interval @Int 1 4 `absorbs` interval 0 4
                assertBool "" . not $ interval @Int 1 4 `absorbs` interval 1 5
                assertBool "" . not $ interval @Int 1 4 `absorbs` interval 2 5
                assertBool "" . not $ interval @Int 1 4 `absorbs` interval 4 5
                assertBool "" . not $ interval @Int 1 4 `absorbs` point 5
            , testCaseSteps "`isRightwardsOf`" \_ -> do
                assertBool "" $ interval @Int 2 4 `isRightwardsOf` interval 1 3
            , testCaseSteps "not `isRightwardsOf`" \_ -> do
                assertBool "" . not $ interval @Int 2 4 `isRightwardsOf` interval 1 5
                assertBool "" . not $ interval @Int 2 4 `isRightwardsOf` interval 2 5
                assertBool "" . not $ interval @Int 2 4 `isRightwardsOf` interval 3 5
                assertBool "" . not $ interval @Int 2 4 `isRightwardsOf` interval 4 5
        ]

        , testGroup "Chains."
            [ testCase "Simple covering chains"
                $ coveringMinimalChains @Int
                    (interval 1 3) [interval 0 3, interval 0 4, interval 1 3, interval 1 4]
                        @?= [[interval 0 3], [interval 0 4], [interval 1 3], [interval 1 4]]
            , testCaseSteps "Non-covering interval set" \_ -> do
                coveringMinimalChains @Int
                    (interval 2 4)
                        [ interval 0 2, point 1, interval 1 2, interval 1 3
                        , point 2, interval 2 3
                        ]
                        @?= [ ]
                coveringMinimalChains @Int
                    (interval 2 4)
                        [ point 3, interval 3 4, interval 3 5
                        , point 4, interval 4 5
                        ]
                        @?= [ ]
                coveringMinimalChains @Int
                    (interval 2 5)
                        [ interval 0 2, point 1, interval 1 2, interval 1 3
                        , point 2, interval 2 3
                        , point 3
                        , point 4, interval 4 5, interval 4 6
                        , point 5, interval 5 6
                        ]
                        @?= [ ]
            , testCase "A set with extra intervals and point join"
                $ coveringMinimalChains @Int
                    (interval 2 5)
                    [interval 1 3, interval 2 4, interval 3 6]
                        @?= [ [interval 1 3, interval 3 6] ]
            , testCase "A set with extra intervals and extended join"
                $ coveringMinimalChains @Int
                    (interval 2 7)
                    [interval 1 4, interval 2 5, interval 3 7]
                        @?= [ [interval 1 4, interval 3 7] ]
            ]
        ]

    , testGroup "Relations."
        [ testProperty "The relation type is isomorphic to the original relation" $
            displayingRelation @Int \xs f rel -> if null (xs :: Set Int) then property True else
                oneOfSet xs \x -> oneOfSet xs \y -> rel ? (x, y) ==  x `f` y
        , testProperty "A relation is not necessarily reflexive" $ expectFailure $
            displayingRelation @Int \_ _ rel -> isReflexive @Int rel
        , testProperty "Reflexive closure of a relation is reflexive" $
            displayingRelation @Int \_ _ rel -> (isReflexive @Int . reflexiveClosure) rel
        , testProperty "A relation is not necessarily symmetric" $ expectFailure $
            displayingRelation @Int \_ _ rel -> isSymmetric @Int rel
        , testProperty "Symmetric closure of a relation is symmetric" $
            displayingRelation @Int \_ _ rel -> (isSymmetric @Int . symmetricClosure) rel
        , testProperty "A relation is not necessarily transitive" $ expectFailure $
            displayingRelation @Int \_ _ rel -> isTransitive @Int rel
        , testProperty "Transitive closure of a relation is transitive" $
            displayingRelation @Int \_ _ rel -> (isTransitive @Int . transitiveClosure) rel
        ]

    , testGroup "Intervals."
        [ testProperty "Shrinking intervals converges (Int)" \i ->
            within (10 ^ (5 :: Int)) . withMaxSuccess 100
            $ let _ = i :: Interval Int
                  nubShrink = fmap List.nub . (>=> shrink)
              in List.elem [ ] . take 1000 . fmap ($ i) . iterate nubShrink $ return
        , testProperty "Shrinking intervals converges (Float)" \i ->
            within (10 ^ (5 :: Int)) . withMaxSuccess 100
            $ let _ = i :: Interval Float
                  nubShrink = fmap List.nub . (>=> shrink)
              in List.elem [ ] . take 1000 . fmap ($ i) . iterate nubShrink $ return
        ]

    , testGroup "Relations on intervals."
        let core = [ precedes, meets, overlaps, isFinishedBy, contains, starts ]
            basic = core ++ fmap flip core ++ [(==)]
        in
            [ testProperty "Exhaustive" \intervals ->
                let _ = intervals :: Set (Interval Float)
                    rels = fmap (relation intervals) basic
                in List.foldl1' (elementwise (+*)) rels == complete intervals
            , testProperty "Pairwise distinct" \intervals ->
                let rels = fmap (relation intervals) basic
                in QuickCheck.withMaxSuccess 1000 do
                    (s, t) <- anyTwo rels
                    return
                        $ counterexample (show s) . counterexample (show t)
                        $ elementwise (*) s t == blank intervals
            ]

    , testGroup "Classification."
        [ testProperty "Union inverts classification" $
            displayingRelation \xs _ rel ->
                let _ = xs :: Set Int
                    equivalence = closure rel
                    classes = classifyBy (curry (equivalence ?)) xs
                in  QuickCheck.classify (Set.size classes > 1) "Non-trivial equivalence" $
                        Set.unions classes == xs
        , testProperty "Intersection of a classification is empty" $
            displayingRelation \xs _ rel -> if Set.null xs then property True else
                let _ = xs :: Set Int
                    equivalence = closure rel
                    classes = classifyBy (curry (equivalence ?)) xs
                in  QuickCheck.classify (Set.size classes > 1) "Non-trivial equivalence" $ property $
                        if Set.size classes == 1 then classes == Set.singleton xs else
                            foldr1 Set.intersection classes == Set.empty
        , testProperty "Belonging to the same class = equivalent by the defining relation" $
            displayingRelation \xs _ rel -> if Set.null xs then property True else
                let _ = xs :: Set Int
                    equivalence = closure rel
                    classes = classifyBy (curry (equivalence ?)) xs
                    g :: Int -> Int -> Bool
                    g = (==) `on` \x -> Set.filter (x `Set.member`) classes
                in  QuickCheck.classify (Set.size classes > 1) "Non-trivial equivalence" $ property $
                        oneOfSet xs \x -> oneOfSet xs \y ->
                        counterexample (show $ Set.filter (x `Set.member`) classes) $
                        counterexample (show $ Set.filter (y `Set.member`) classes) $
                        counterexample (show equivalence) $
                            equivalence ? (x, y) == (x `g` y)
        , testProperty "Every element belongs to exactly one class" $
            displayingRelation \xs _ rel -> if Set.null xs then property True else
                let _ = xs :: Set Int
                    equivalence = (transitiveClosure . symmetricClosure . reflexiveClosure) rel
                    classes = classifyBy (curry (equivalence ?)) xs
                in  QuickCheck.classify (Set.size classes > 1) "Non-trivial equivalence" $ property $
                        counterexample (show classes) $ counterexample (show equivalence) $
                            length (Set.unions classes) == (sum . fmap length . Set.toList) classes
        ]

    ,  testGroup "Normalizer."
        [ testProperty "Normal set of intervals is pairwise disjoint" \s ->
            let t = normalize s :: Set (Interval Float)
            in QuickCheck.classify (s /= t) "Non-trivial normalization"
                . counterexample (displayIntervals s) . counterexample (displayIntervals t)
                $ if Set.size t < 2 then return True else do
                    (i, j) <- anyTwo t
                    return $ i `isDisjointWith` j
        , testProperty "Normalization is idempotent" \s ->
            QuickCheck.classify (normalize s /= s) "Non-trivial normalization"
            let t = normalize s :: Set (Interval Float)
                t' = normalize t
            in  counterexample (displayIntervals s) . counterexample (displayIntervals t)
                . counterexample (displayIntervals t')
                $ t == t'
        , testProperty "Preserves pointwise coverage" $ \s x ->
            let t = normalize s :: Set (Interval Float)
            in  QuickCheck.classify (countWithin s x == 1) "Point is within exactly once"
                . QuickCheck.classify (t /= s) "Non-trivial normalization"
                . QuickCheck.classify (countWithin s x > 1) "Point is within more than once"
                .  QuickCheck.classify (not $ x `isWithinOneOf` s) "Point is without"
                . counterexample (displayIntervals s) . counterexample (displayIntervals t)
                $ (countWithin s x >= 1) == (countWithin t x == 1)
        ]

    , checkCommutativeRingAxioms (Proxy @Binary) "Binary"
    , checkCommutativeRingAxioms (Proxy @(Interval Float -> Interval Float -> Bool))
        "Interval a -> Interval a -> Bool"

    , testGroup "Chains."
        [ checkSolution coveringChains (Proxy @Int) "`coveringChains` (Int)"
        , checkSolution coveringChains (Proxy @Float) "`coveringChains` (Float)"
        , checkSolution coveringChainsFromTo (Proxy @Int) "`coveringChainsFromTo` (Int)"
        , checkSolution coveringChainsFromTo (Proxy @Float) "`coveringChainsFromTo` (Float)"
        , checkSolution willemPaths (Proxy @Int) "`willemPaths` (Int)"
        , checkSolution willemPaths (Proxy @Float) "`willemPaths` (Float)"
        ]
    ]

checkSolution :: forall a. (Show a, NFData a, Arbitrary (Interval a), Num a, Ord a)
              => (Interval a -> [Interval a] -> [[Interval a]]) -> Proxy a -> String -> TestTree
checkSolution solution Proxy solutionName = testGroup ("Chains: " ++ show solutionName ++ ".")
        [ testProperty "A chain terminates" \base intervals ->
            let _ = intervals :: [Interval a]
                chains = solution base intervals
            in within (10 ^ (4 :: Int)) . withMaxSuccess 1000
                $ chains `deepseq` True
        , testProperty "A normalized chain is a singleton" \base intervals ->
            let _ = intervals :: [Interval a]
                normalChains = fmap normalizeList (solution base intervals)
            in counterexample (show normalChains)
                $ and . fmap ((1 ==) . length) $ normalChains
        , testProperty "A chain is a cover" \base intervals ->
            let _ = intervals :: [Interval a]
                chains = Set.fromList . fmap (normalize . Set.fromList) $ solution base intervals
            in and . Set.map (`subsume` base) $ chains
        , testProperty "A chain is minimal" \base intervals ->
            let _ = intervals :: [Interval a]
                chains = solution base intervals
                subchains = List.nub (chains >>= dropOne)
            in within (10 ^ (6 :: Int)) $ (or . fmap ((`subsume` base) . Set.fromList)
                $ fmap normalizeList subchains) == False
        , testProperty "Brute force search on null chain situations is fruitless"
            \base intervals3 ->
             let intervals2 = getInfiniteList intervals3 :: [[Interval a]]
                 f = List.null . solution base
                 g = \xs -> length xs < 10
                 Just intervals = List.find f . filter g . take 100 $ intervals2
             in counterexample (show intervals)
                $ length intervals > 7 ==> List.null (bruteForceCoveringChains base intervals)
        ]

willemPaths :: Ord a => Interval a -> [Interval a] -> [[Interval a]]
willemPaths u us = (fmap.fmap) fromTuple $ paths' (toTuple u) (fmap toTuple us)
  where
    toTuple (Interval x y) = (x, y)
    toTuple (Point x) = (x, x)
    fromTuple = uncurry interval

-- Example errors:
-- λ paths' (0, 2) [(-2, 1), (-1, 2)]
-- [[(-2,1),(-1,2)],[(-1,2)]]
-- λ paths' (-2, 1) [(-2, 1), (-3, -1)]
-- [[(-3,-1),(-2,1)],[(-2,1)]]

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
