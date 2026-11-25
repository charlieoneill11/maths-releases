# A distance-two pair in the nonadjacent 113 case

A four-dimensional packing of size 113 cannot have a pair of full bands
at start distance two on each axis when the full bands on each axis are
pairwise nonadjacent. A full band contains 33 words. The same enumeration
excludes the three remaining unordered profiles with a distance-two source
and transverse gaps in two and three. These four exclusions use the size-113
condition. The proof allows ten-word planar crossings and unrestricted lifts
on every band. [Mixed-profile census](mixed.md)

Use coordinates A, B, C, D. Choose the distance-two starts on A to be 0 and
2. Their three-dimensional projections \(S,T\) have size 33. An isometry on
B, C, D carries \(S\) to one of the 1,016 representatives in the complete
atlas. For each representative the checker tries every distinct physical
image of \(T\), 16,672,544 in total. Signs and permutations used to normalize
\(S\) may exchange the order of marked starts on any transverse axis. Trying
all seven starts of each pair handles both orders. [Maximum three-dimensional atlas](../../round25/multiplicities/atlas/README.md)

## Planar crossing requirements

For a transverse mark starting at \(t\), erase that transverse coordinate.
Its 33-word projection must give precisely the planar cut of \(S\) at \(t\)
on A-levels 0,1 and the cut of \(T\) at \(t\) on A-levels 2,3. The checker
collects every possible ordered pair of such cuts from the atlas, using
all longitudinal axes, translations, both directions and all 392 planar
isometries. For each physical \(T\), bit sets identify every \(S\) with a
pair of individually admissible marks on all three transverse axes. For
transverse gaps 2,2,2 this reduces 16,939,304,704 pairs to 9,767,343.
[Planar filter](candidate_pairs.cpp)

## Matching through four physical levels

Write \(X\subseteq S\) and \(Y\subseteq T\) for the projections at A-levels 1
and 2. The two sets are disjoint and their union is independent. The
seven A-band sizes sum to 226. There are either two or three full bands,
because full starts are nonadjacent. With two full bands the five others
have size 32. With three, the four others have sizes 31, 32, 32, 32. Thus
\(|X|+|Y|\ge31\). Every single level has between 14 and 19 words. Its
complement partitions into three bands of size at most 33, and an adjacent
level has size at least 14.

Make a bipartite graph on \(S,T\) by joining every pair at cyclic distance
at most one in every coordinate, including equal words. If a subset of
\(S\) had fewer neighbors in \(T\) than its size, combining it with all
nonneighbors in \(T\) would give a packing larger than 33. Hall's theorem
therefore gives a perfect matching, which the checker constructs directly.
At most one endpoint of each matched edge belongs to \(X,Y\), so at most two
matched edges have neither endpoint chosen.

For each individual transverse mark the atlas also supplies the possible
A-levels 1 and 2 within its two planar contacts. Each planar contact lifts
injectively to the points of its marked cut of \(S\) or \(T\). Assemble
these local membership assignments over six transverse marks. Whenever
two marks prescribe the same physical word on the same shore, they must
agree. Reject a partial assignment if it chooses both endpoints of a
matched edge, already leaves three edges empty, or makes the 14-to-19
bounds impossible on either shore. An accepted layout records the two
source projections and the transverse starts. Subsequent enumeration
reconsiders all physical supports at that layout. For transverse gaps 2,2,2,
25,578,139 placements enter this test and just 894 survive, representing 889
distinct normalized projection pairs. [Matching test](match_middle.cpp)

## Joining actual transverse projections

For each of six marks, retain every physical 33-word projection with the
two required A-contacts. The checker generates all 16,464 orientations and
translations per atlas representative, deduplicating only identical physical
projections within a mark. When two marks lie on different axes, their
planar projections on the common crossing must agree. On each shore all
chosen projections must prescribe consistent membership in \(X,Y\).
Additionally, no prescribed point of \(X\) can conflict with any prescribed
point of \(Y\), since their A-levels are adjacent. Exhaustive search visits
194,290 compatible prefixes for transverse gaps 2,2,2 and finds zero complete
products. All these tests are necessary for an actual packing.
[Physical projection join](join_projections.cpp)

For an independent geometrical check, the audit moves all 33 coordinates
of every atlas image explicitly. It builds the marked projections from
physical rows and tests pairwise compatibility before an exhaustive join.
In the separate gap-two replay, planar agreement alone leaves 125 of the
894 candidate layouts. Including the A-level memberships and conflicts
eliminates all 125. In the combined run for transverse gaps 2,2,3, 2,3,3 and
3,3,3, one of the 17,702 layouts allows planar agreement and its middle
levels are incompatible. [Direct-coordinate audit](audit_projections.cpp)

The same checker accepts a separate size-112 hypothesis with two middle
levels of exactly 15 words. It excludes every 112-word packing with at
least two full bands on every axis. [Size-112 proof](target112.md)

## Replay

From this directory run the Python driver with a C++17 compiler available.
The driver builds four executables, enumerates from the atlas in a fresh
temporary directory, checks both intermediate ledgers, and requires the
final assignment file to be empty.

```sh
python3 verify.py --mode 2222
python3 verify.py --mode mixed
```
