# Adjacent full 33-bands in four dimensions

**No 113-word independent set in the fourth strong power of the seven-cycle has two consecutive full bands on every axis.** A full band contains 33 words on two consecutive coordinate levels. Here two consecutive bands have level sets $\{c-1,c\}$ and $\{c,c+1\}$, so they share level $c$. The theorem applies under ordinary independence alone, including packings with ten-word planar windows. The other fourteen possible profiles are excluded separately. Full proof of the unrestricted bound of 112

The computation proves an exact result independent of the target 113. Suppose that on each of the four axes one can select consecutive full bands sharing **16 through 19 words**. Then the entire packing has **at most 105 words**. An example attaining 105 has 19 words on each selected shared level. [Physical 105-word example](example-105.txt)

## Why this excludes the all-adjacent 113 case

Fix an axis, write $h_i$ for its layer sizes and put $d_i=33-h_i-h_{i+1}$, with indices modulo seven. Projecting a band off its restricted axis preserves independence and cardinality. The three-dimensional maximum is 33, so the deficits are nonnegative. At total size 113 they sum to five, and the odd-cycle equations give

$$
h_i=14+d_{i+1}+d_{i+3}+d_{i+5}.
$$

A shared level between two consecutive full bands has $d_{i-1}=d_i=0$. Of the 462 labelled nonnegative seven-vectors summing to five, 420 have consecutive zeros. On those 420 vectors the largest eligible $h_i$ is 16, 17, 18 or 19 in 14, 147, 154 and 105 cases, respectively. Consequently, if every axis has consecutive full bands, one can choose a shared level of size 16 through 19 on each axis independently. The checker regenerates these counts. [Profile and witness checks](verify.py)

## Enumerating one physical slab

Choose the first axis and put its three marked levels at $0,1,2$. Let $S$ and $T$ be the three-dimensional supports obtained by projecting the two full bands. Each is an independent 33-set. Write $U$ for the projection of the physical middle level. Then $U\subseteq S\cap T$. The three physical levels are uniquely specified by

$$
S\setminus U,\qquad U,\qquad T\setminus U.
$$

In particular, a site of $(S\cap T)\setminus U$ carries both an outer-level word at 0 and an outer-level word at 2. The four-dimensional slab has $66-|U|$ words.

The complete atlas of independent 33-sets has 1,016 isometry classes. Fix $S$ as a representative and let $T$ range over all 16,672,544 labelled images, removing duplicates by equality of the physical support. The images use every axis permutation, reflection and translation of the three-torus. We retain all 21,103,868 ordered pairs with $|S\cap T|\ge16$. This normalization keeps all ways of placing $T$ relative to $S$, including placements related by a stabilizer of $S$. [Complete atlas and regeneration](../../round25/multiplicities/atlas/README.md) · [Ordered support pairs](pair_supports.cpp)

Consider a marked transverse band on one of the remaining axes. Its cuts through $S$ and $T$, projected along that transverse axis, give planar masks $X$ and $Y$. In the transverse 33-set these must be projections of two consecutive bands. The checker tabulates such pairs in both orders and under every planar isometry. A transverse axis must have two consecutive starts passing this test.

For each allowed $(X,Y)$ the atlas also gives every possible middle-layer mask $M$. The two-level cut of $S$ projects injectively, so its planar sites identify particular sites of $S$. On this cut, $M$ prescribes exactly which sites belong to $U$. Assignments for two starts on the same axis and for starts on different axes must agree wherever they overlap. The checker joins these restrictions, enumerates all subsets of the uncovered sites in $S\cap T$, and keeps $16\le |U|\le19$. This leaves 17,706,755 choices of a support pair, three transverse centers and a physical middle. [Contact test](filter_contacts.cpp) · [Middle enumeration](middle_layers.cpp)

## Checking the six transverse bands

For a fixed middle, the first three layers of each transverse support are exactly $(X\setminus M,M,Y\setminus M)$. We look up every atlas image with that ordered prefix. Hashes locate candidates, and equality of all three masks determines membership. For transverse supports with different axes, their projected crossing must agree as a planar mask. For supports on the same transverse axis, the already fixed words on their shared level plus the common support available on the four outside first-axis levels must reach 16. An exhaustive six-way join tests these necessary conditions simultaneously.

Precisely **2,852** of the middle choices admit at least one six-way match. Each surviving record keeps its physical three-level slab. The later construction allows all compatible slabs from this list, so one successful six-way match suffices for each record. The counts in the final column of the census count these records. [Exact six-way join](join_bands.cpp) · [Census by projected intersection size](census.tsv)

In particular, no projected intersection size of 16, 17, 18, 19, 32 or 33 survives. For the smallest possible intersection, $U=S\cap T$ is forced. Of the 6,477,540 pairs of this size, only two normalized pairs and center choices reach the six-way test. A second checker takes these two candidates from the output of the middle enumeration and redoes the six-band step for them, generating their transverse domains directly from physical coordinates. It does not regenerate the candidates themselves. Their six domain sizes are $(20,33,26,18,9,3)$ and $(3,9,18,26,33,20)$, and the replay asserts both lists. In both cases two bands on different axes have no common crossing. [Independent six-band check at overlap 16](check_pinned.cpp)

## Matching the four physical slabs

Translate the four chosen centers to zero. Each marked slab now has levels $\{6,0,1\}$ on its normal axis. For the first axis retain the normalized slab as recorded. For each of the other axes, orient the same exhaustive list by every signed coordinate permutation taking its normal to that axis. All remaining translations are fixed by the choice of four centers. This gives 2,852 distinct first slabs and 136,896 slabs on each of the other axes.

Slabs on two axes must contain exactly the same physical four-coordinate sites in their common region. Repeatedly discarding a slab with no matching partner in another direction leaves domains of sizes 2,004, 1,655, 1,809 and 2,570. The checker joins all four directions, comparing complete intersections and testing every cross-slab pair for independence. The 1,776 surviving unions are distinct in this normalization. Each determines every word of the packing that has any coordinate in $\{6,0,1\}$. [Physical slab join](join_slabs.cpp)

## Exact exterior completion

All additional words have all four coordinates in $\{2,3,4,5\}$. Remove sites that conflict with the slab union. Among the remaining sites, branch on including or excluding a site $v$. The inclusion branch also removes every neighbor of $v$. The two branches exhaust all possibilities, and an independent remainder is its own maximum. The checker verifies that every maximizing extension it returns is physically independent. It also checks all eight 33-word marks and the sizes of all four shared levels in each input union.

Of the initial unions, 720 have 97 words, 736 have 98, 280 have 99 and 40 have 100. The following counts give the exact optimum after adding exterior words. [Exact exterior search](exterior.py)

| Maximum completed size | Number of slab unions |
|---:|---:|
| 101 | 24 |
| 102 | 80 |
| 103 | 1,328 |
| 104 | 320 |
| 105 | 24 |

## Replay

Run from this directory with Python 3.10 or later and a C++17 compiler. The driver checks the hash of the published atlas, rebuilds all intermediate lists in a temporary directory, compares the full overlap census, and checks the extremal example directly. The intermediate lists use about 650 MB of disk.

~~~
python3 -B verify.py
~~~

Mixed distances use the same atlas and middle constraints with the indicated transverse separations. [Mixed-distance exclusions and replay](mixed.md) · [Transfer to 112-word band profiles](transfer112.md)
