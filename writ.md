### This is actually a problem of some depth.

Or, rather, the algorithm you ask for is simple _(if approached with the right tools at hand)_; but checking whether it is correct is not, and it is very easy to make a slight mistake. This is because intervals are unlike numbers in that there is no such simple notion as the usual total order anymore, and what relations we have instead are tenfold more complex — too far so for the unarmed human mind to grasp.

### So, let us arm ourselves.

With numbers _(or single points)_, there are only 3 disjoint qualitative relations: `a < b` or `a = b` or `a > b`. What can we say about pairs of numbers _(representing intervals)_ then? There are 5 places a point can be with respect to an interval:

                 on the left end
                 v
    -- before -- * == inside == * -- after --
                                ^
                                on the right end

Considering that the left end of an interval is never to the right of its right end, this gives us `sum [5, 4.. 1] = 15` disjoint qualitative relations between two intervals. Disregarding the two relations where both ends of one interval are on the same end of another _(meaning the interval is a point)_, that gives 13. And now there is a [prior art][1] discussing exactly 13 disjoint exhaustive relations on intervals. _([Original article.][2])_

[1]: https://www.ics.uci.edu/~alspaugh/cls/shr/allen.html
[2]: https://cse.unl.edu/~choueiry/Documents/Allen-CACM1983.pdf

Namely, James Allen defines these 6 relations:

* Precedes.
* Meets.
* Overlaps.
* IsFinishedBy.
* Contains.
* Starts.

Together with their inversions and the equality relation. It is tedious and straightworward to encode any of them in Haskell.

Whereas for numbers we can only derive 8 composite relations in terms of the 3 fundamental, on intervals we can define about 8 _thousand_. Some of them will be of use to us within this problem, so let me list those too, for reference:

* _"Is disjoint with"_ = precedes or is preceded by. In the language of set theory, that means they have no common point.
* _"Absorbs"_ = is finished by or contains or is started by or equals. In set theory, that means every point in the second interval is also in the first.
* _"Touches"_ = meets or overlaps. Graphically, that means that one interval connects to the other by some points, in a specific direction.
* _"Is rightwards of"_ = is touched by or is preceded by. In the set language, there are some points in one interval that extend farther to the right than any point of the other.



Outline:

1. We need to be able to check.
1. Relations on intervals.
1. Transitive closure and the introduction of the check.
1. Definition of chain.
1. Actual code.
