module Willem where

import Data.List (sort)

paths1 :: Ord a => (a, a) -> (a, a) -> [(a, a)] -> [[(a, a)]]
paths1 (a, f) (b, c) _ | c >= f = [[]]
paths1 _ _ [] = []
paths1 r s@(b, c) ((d, e):xs) | d > c = []
                              | d <= b || e <= c = paths1 r s xs
paths1 r s@(_,sb) (x@(_, xb):xs) = map (x:) (paths1 r (sb,xb) xs) ++ paths1 r s xs

paths0 :: Ord a => (a, a) -> [(a, a)] -> [[(a, a)]]
paths0 (a, _) ((b, _):_) | b > a = []
paths0 r@(a, _) ((_, c):xs) | c <= a = paths0 r xs
paths0 r (x:xs) = map (x:) (paths1 r x xs) ++ paths0 r xs

paths :: Ord a => (a, a) -> [(a, a)] -> [[(a, a)]]
paths = (. sort) . paths0
