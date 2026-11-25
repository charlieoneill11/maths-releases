# Two 33-bands at distance three on all four axes

No four-dimensional packing has two 33-word adjacent bands at cyclic start distance three on every axis. In particular, this excludes the marking profile $(3,3,3,3)$ for a 113-word packing. The proof uses only the eight full projections and the requirement that their planar crossings agree. It applies for any total population.

Normalize the marked starts on each axis to 0 and 3. Restrict a packing to a marked two-level band and erase the restricted coordinate. The resulting three-dimensional support has 33 words and is independent, since both possible erased coordinates are near. It is an image of one of the [1,016 atlas representatives](../../round25/multiplicities/atlas/README.md). Two projections on transverse axes must induce identical planar masks on their common crossing. The two free planar coordinates retain their order and their physical residue labels.

## Exhausting the eight projections

For each image of an atlas representative, record its six planar masks at starts 0 and 3 on each of its three axes. Write $G$ for the relation on ordered pairs of masks that occur at both designated starts of one axis of one image. The census produces 138,670 different masks and 4,145,792 ordered pairs in $G$. The search uses every signed coordinate permutation and translation. Retaining repeated motions from nontrivial stabilizers leaves every possible support available.

Choose one of the eight full projections with the least atlas class index. Move its band to the first axis and start zero. Its support $S$ can be taken to be a translation of its atlas representative. Indeed, permuting the remaining axes and applying independent reflections $x\mapsto4-x$ preserves the two designated starts as an unordered pair and realizes any signed linear part. There are $1016\cdot343=348{,}488$ representative and translation choices.

Let $T$ be the other full projection on the first axis. For each of the six transverse marked bands $j$, the corresponding ordered mask pair $(S_j,T_j)$ must lie in $G$. The checker indexes the atlas images by pairs of masks. For each $S$ it looks up the least frequent two requirements and tests all four remaining requirements on every matching $T$ whose class index is at least that of $S$. This ordering only changes the work performed by the lookup.

For a surviving $(S,T)$, the domain of transverse band $j$ consists of every atlas image with $(S_j,T_j)$ on its first axis. The other four cuts of the image give its possible contacts with bands on the two remaining transverse axes. A 64-bit signature records hashed mask IDs in each domain. Disjoint signatures rule out a common mask. Exhaustive backtracking compares the exact mask IDs on all twelve transverse crossings between these six bands. The two bands on each parallel axis have no compatibility requirement in this test.

Among the 348,488 source placements, 143,566 have no six-contact partner and 204,922 have at least one. The search describes each $T$ by an atlas class and a motion, and finds **21,633,276** such descriptions of six-contact pairs. Two descriptions of the same support differ by an element of the stabilizer of its class. The program identifies them by comparing the moved coordinates and counts **21,378,687** distinct pairs $(S,T)$. The 254,589 repeated descriptions all come from the five classes with nontrivial stabilizers, and for every class the number of descriptions is the stabilizer order times the number of distinct supports. No pair admits the other six projections. Before the search, the program checks actual transformed coordinates against the mask index for every pair of one of the 1,016 classes and one of the 16,464 motions.

## The full bands on one axis

Every four-dimensional packing has an axis whose full-band starts are contained in three consecutive residues. On at least one axis the set $F$ of full starts has no pair at distance three. Such an $F$ is independent on the seven-cycle with step three and therefore has at most three elements. An independent triple in the step-three order has successive gaps $2,2,3$ up to rotation. In the ordinary order this gives three consecutive residues. Any allowed pair has ordinary distance one or two and likewise fits in three consecutive residues.

At least four bands on this axis have size at most 32, so twice the total population is at most $7\cdot33-4=227$. Thus the gap-three exclusion alone gives the ordinary upper bound 113. At total 113 the deficits sum to five. There are four dihedral possibilities on this axis. Two full starts can be at distance one or two, in which case all other bands have size 32. Three consecutive full starts leave one band of size 31 and three of size 32, with two possible positions for the size-31 band up to reflection.

At total 112 write $d_i=33-|B_i|$ on this axis, where $B_i$ is the band starting at $i$. The deficits sum to $7\cdot33-2\cdot112=7$, and their zeros form $F$. The 393 possible labelled deficit profiles from these conditions have the following counts. Each chosen $F$ leaves a composition of seven into $7-|F|$ positive parts.

| Full starts | Choices of $F$ | Labelled profiles |
|---:|---:|---:|
| 0 | 1 | 1 |
| 1 | 7 | 42 |
| 2 | 14 | 210 |
| 3 | 7 | 140 |

These are 32 dihedral classes. Each of the six nonidentity rotations fixes only the constant profile of ones. For a reflection, its single fixed residue has an odd deficit. The zeros are therefore empty or one reflected pair. Of the three reflected pairs, two have allowed ordinary distance one or two. For each of them the remaining two reflected-pair deficits $a,b$ are positive and the fixed residue has deficit $7-2a-2b>0$, giving three possibilities. Thus each reflection fixes seven profiles, and Burnside's count is $(393+6+7\cdot7)/14=32$.

## Replay

From the upper113 directory, run with a C++17 compiler and assertions enabled. The optional final arguments specify a half-open interval of atlas class indices for a partial replay.

```sh
c++ -O3 -std=c++17 gap_three.cpp -o /tmp/c7-gap-three
/tmp/c7-gap-three ../../round25/multiplicities/atlas/atlas.tsv
```

## Independent recount

[`gap_three_check.cpp`](gap_three_check.cpp) repeats the search without the mask index and shares no code with `gap_three.cpp` or `atlas.hpp`. It lists all 16,672,544 labelled 33-sets as explicit sets of points, removes repeated images by comparing the sets, computes every cut from coordinates, and searches the pairs $(S,T)$ with $S=R+v$ and the six transverse domains directly. For each atlas class of $S$ it prints the numbers of translates with no partner and with some partner and the number of distinct pairs. These agree class by class with the cumulative counts printed by `gap_three.cpp` (the fields after the class index are the placements with a partner, those without, the lookups, the descriptions, and, after `distinct`, the distinct pairs). It finds 21,378,687 distinct pairs and no pair admitting the six projections. It is not part of `verify_upper_bound.py`; the recorded run, compiled with `-march=native` added, took about 25 minutes on one core with 1.1 GB of memory.

```sh
c++ -O3 -std=c++17 gap_three_check.cpp -o /tmp/c7-gap-three-check
/tmp/c7-gap-three-check ../../round25/multiplicities/atlas/atlas.tsv
```
