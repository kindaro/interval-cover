### This is actually a problem of some depth.

Or, rather, the algorithm you ask for is simple _(if approached with the right tools at hand)_;
but checking whether it is correct is not, and it is very easy to make a slight mistake. This is
because intervals are unlike numbers in that there is no such simple notion as the usual total
order anymore, and what relations we have instead are tenfold more complex — too far so for the
unarmed human mind to grasp.

1. We need to understand how intervals relate to each other.
2. We need to be able to check if a given set of intervals is a solution to the problem.

I will be saying _"base"_ meaning the interval to be covered, and _"chain"_ consisting of _"links"_ meaning a set of intervals that may be covering it. _(This naming will be justified somewhere below.)_

### So, let us arm ourselves.

With numbers _(or single points)_, there are only 3 disjoint qualitative relations: `a < b` or `a
= b` or `a > b`. What can we say about pairs of numbers _(representing intervals)_ then? There are
5 places a point can be with respect to an interval:

                 on the left end
                 v
    -- before -- * == inside == * -- after --
                                ^
                                on the right end

Considering that the left end of an interval is never to the right of its right end, this gives us
`sum [5, 4.. 1] = 15` disjoint qualitative relations between two intervals. Disregarding the two
relations where both ends of one interval are on the same end of another _(meaning the interval is
a point)_, that gives 13. And now there is a [prior art][1] discussing exactly 13 disjoint
exhaustive relations on intervals. _([Original article.][2])_

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

    absorbs         =  isFinishedBy `or` contains      `or` flip starts `or` (==)
    isDisjointWith  =  precedes     `or` flip precedes
    joins           =  (fmap . fmap) not isDisjointWith
    touches         =  meets        `or` overlaps
    isRightwardsOf  =  flip (precedes `or` touches)
    ...

Given these relations, we can manipulate them to obtain all kinds of awesome devices, such as
closures, equivalences and orders. I will presently use some of these to verify solutions to our
problem.

1. A reflexive, symmetric and transitive closure of `joins` is an equivalence under which
   considered equivalent are those intervals that belong to a contiguous line.
2. A _normal_ set of intervals is such in which all intervals are disjoint.
    * Any set may be _normalized_ by gluing together intervals that `join` until none are left.
    * Normalization preserves coverage: if a point belongs to some of the intervals in a set, it
      will belong to an interval in its normalization.
3. A solution is a chain such that:
    * Its normalization is a singleton set whose only member `absorbs` the base. _(Sufficient.)_
    * With any link removed, this condition does not hold. _(Minimal.)_

Therefore, `normalize` is a function that divides a set of intervals into classes of equivalence
induced by `joins` and converts each class to an interval by taking the extrema of all the
endpoints.

    relation :: Ord a => Set a -> (a -> a -> Bool) -> Relation a

    closure :: Relation a -> Relation a

    classifyBy :: Ord a => (a -> a -> Bool) -> Set a -> Set (Set a)

    (?) :: Eq a => Relation a -> (a, a) -> Bool

    bounds :: Set Int -> I

    flatten :: Set I -> Set Int

    normalize :: Set I -> Set I
    normalize u | Set.null u = Set.empty
                | otherwise = let  rel = closure (relation u joins)
                                   classes = classifyBy (curry (rel ?)) u
                              in Set.map (bounds . flatten) classes


Outline:

1. We need to be able to check.
1. Relations on intervals.
1. Transitive closure and the introduction of the check.
1. Definition of chain.
1. Actual code.
