### This is actually a problem of some depth.

Or, rather, the algorithm you ask for is simple _(if approached with the right tools at hand)_;
but checking whether it is correct is not, and it is very easy to make a slight mistake. This is
because intervals are unlike numbers in that there is no such simple notion as the usual total
order anymore, and what relations we have instead are tenfold more complex — too far so for the
unarmed human mind to grasp.

1. We need to understand how intervals relate to each other.
2. We need to be able to check if a given set of intervals is a solution to the problem.

I will be saying _"base"_ meaning the interval to be covered, and _"chain"_ consisting of
_"links"_ meaning a set of intervals that may be covering it. _(I will eventually justify this
naming.)_

### So, let us arm ourselves.

With numbers _(or single points)_, there are only 3 disjoint qualitative relations: `a < b` or `a
= b` or `a > b`. What can we say about pairs of numbers _(representing intervals)_ then? There are
5 places a point can be with respect to an interval:

                 on the left end
                 v
    -- before -- * == inside == * -- after --
                                ^
                                on the right end

Considering that the left end of an interval is never to the right of its right end _(duh)_, this
gives us `sum [5, 4.. 1] = 15` disjoint qualitative relations between two intervals. Disregarding
the two relations where both ends of one interval are on the same end of another _(meaning the
interval is a point)_, that gives 13. And now there is a [prior art][1] discussing exactly 13
disjoint exhaustive relations on intervals. _([Original article.][2])_

[1]: https://www.ics.uci.edu/~alspaugh/cls/shr/allen.html
[2]: https://cse.unl.edu/~choueiry/Documents/Allen-CACM1983.pdf

Namely, James Allen defines these 6 relations:

    precedes      =  \ i j  ->  right i < left j
    meets         =  \ i j  ->  right i == left j && left i /= left j && right i /= right j
    overlaps      =  \ i j  ->  left i < left j  && right i < right j && right i > left j
    isFinishedBy  =  \ i j  ->  left i < left j  && right i == right j
    contains      =  \ i j  ->  left i < left j  && right i > right j
    starts        =  \ i j  ->  left i == left j && right i < right j

— Together with their inversions `flip ...` and the equality relation.

Whereas for numbers we can derive exactly 8 composite relations in terms of the 3 basic ones
_(considering relations as a vector space over the binary field)_, on intervals we can define
about 8 _thousand_. Some of those will be of use to us within this problem:

    absorbs         =  isFinishedBy `or` contains `or` flip starts `or` (==)
    isDisjointWith  =  precedes     `or` flip precedes
    joins           =  (fmap . fmap) not isDisjointWith
    touches         =  meets        `or` overlaps
    isRightwardsOf  =  flip (precedes `or` touches)
    ...

Given these relations, we can manipulate them to obtain all kinds of awesome devices, such as
closures, equivalences and orders. I will presently use some to obtain a verifier of solutions to
our problem.

1. A reflexive, symmetric and transitive closure of `joins` is an equivalence under which
   considered equivalent are those intervals that belong to a contiguous line. _(While not
   necessarily being adjacent on that line.)_
2. A _normal_ set of intervals is such in which all intervals are disjoint.
    * Any set may be _normalized_ by gluing together intervals that join until none are left.
    * Normalization preserves coverage: exactly when a point belongs to some of the intervals in a
      set, it will belong to some interval in its normalization.
3. A solution is a chain such that:
    * Its normalization is a singleton set whose only member `absorbs` the base. _(Sufficient.)_
    * With any link removed, this condition does not anymore hold. _(Minimal.)_

Therefore, `normalize` is a function that divides a set of intervals into classes of equivalence
induced by `joins` and converts each class to an interval by taking the extrema of all the
endpoints.

    relation :: Ord a => Set a -> (a -> a -> Bool) -> Relation a

    closure :: Relation a -> Relation a

    classifyBy :: Ord a => (a -> a -> Bool) -> Set a -> Set (Set a)

    (?) :: Eq a => Relation a -> (a, a) -> Bool

    bounds :: Ord a => Set a -> Interval a

    flatten :: Ord a => Set (Interval a) -> Set a

    normalize :: Ord a => Set (Interval a) -> Set (Interval a)
    normalize u | Set.null u = Set.empty
                | otherwise = let  rel = closure (relation u joins)
                                   classes = classifyBy (curry (rel ?)) u
                              in Set.map (bounds . flatten) classes


In these terms, we can define the check:

    isCovering :: Ord a => Interval a -> [Interval a] -> Bool
    isCovering base xs = case (Set.toList . normalize . Set.fromList) xs of
                            [y] -> y `absorbs` base
                            _   -> False

    isMinimalCovering :: Ord a => Interval a -> [Interval a] -> Bool
    isMinimalCovering base xs = sufficient && minimal
        where sufficient = isCovering base xs
              minimal    = List.null . filter (isCovering base)
                                     . fmap (`deleteAt` xs) $ [0.. length xs - 1]

Not only that, we can define a filter:

    bruteForceCoveringChains :: forall a. (Ord a, Num a)
                             => Interval a -> [Interval a] -> [[Interval a]]
    bruteForceCoveringChains base xs = filter (isMinimalCovering base) (List.subsequences xs)

The complexity of these devices is crazy. Empirically, this brute force solution can munch through
a set of 10 intervals, but not 20. But this much is enough to check a candidate fast algorithm
against.

### Onwards now!

All the links in our chain must connect, like... links of a chain. One after the other. There is a
relation for that: the one I named `touches`. If a series of intervals consecutively touch one
another, we are certain that they cover the space from the beginning of the first to the ending of
the last one. We can use this relation to consecutively filter more and more links into our chain
until it subsumes the base completely.

Incidentally, `touches` is an antisymmetric relation, which makes its transitive and reflexive
closure an _ordering_ of intervals, and a _chain_ in order theory is exactly a totally ordered
set. So, our naming is justified: there is a relation that is not a total ordering for arbitrary
sets of intervals, but is a total ordering for our chains.

This is not enough though: we must also ensure our chain is minimal. I claim that this condition
holds exactly when `touches` is _nowhere transitive_. That means: when <code>x `touches` y</code>
and <code>y `touches` z</code>, it is never that <code>x `touches` z</code>. If it were, we would
not need `y` in our chain. Observe that, like links in a real chain, our _"links"_ must only
overlap two at a time. This requirement may be paraphrased in terms of interval relations: a link
must _be touched by_ the interval between the end of the previous link and the one before the
previous. It sounds a bit baroque, but I am sure the reader may depict this situation in their
mind or on a piece of paper.

This is all that is needed to give a recursive definition that we are looking for.


Outline:

1. We need to be able to check.
1. Relations on intervals.
1. Transitive closure and the introduction of the check.
1. Definition of chain.
1. Actual code.
