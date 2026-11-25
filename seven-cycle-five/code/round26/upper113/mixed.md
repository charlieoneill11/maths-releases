# Mixed distances between full 33-bands

A full band has 33 words on two successive levels of a four-dimensional independent set. On each axis choose two full bands that minimize the circular distance between their starting levels. Sort the four distances to describe the profile. Every axis of a 113-word packing has at least two full bands, since the seven band deficits are nonnegative and sum to five.

The checker below treats profiles that have an adjacent pair on at least one axis. On every such axis the deficit census gives a choice of adjacent bands with 16 through 19 words on their common level. Distances two and three require two disjoint full bands. Their physical levels and their projections can vary independently of the two other marks until geometric compatibility is tested. The method uses the unrestricted three-dimensional maximum of 33 and allows ten-word planar windows. [Deficit calculation and support atlas](README.md)

## Recorded exclusions

Each row excludes a complete four-dimensional 113-word distance profile. The final column counts the unions that reached the test of the remaining full-band projections. That test excluded every such union.

| Distances | Physical middle choices | Six-band matches | Independent slab unions |
|---|---:|---:|---:|
| 1112 | 20,680,742 | 138 | 0 |
| 1113 | 8,870,883 | 0 | 0 |
| 1122 | 7,027,895 | 48 | 4 |
| 1123 | 7,323,911 | 395 | 64 |
| 1133 | 1,806,905 | 0 | 0 |
| 1222 | 953,888 | 0 | 0 |
| 1223 | 1,499,193 | 0 | 0 |
| 1233 | 990,374 | 0 | 0 |
| 1333 | 194,256 | 0 | 0 |

## Marked starts and physical slabs

Normalize a distinguished adjacent pair and its two projected 33-sets as in the all-adjacent proof. On a transverse axis of distance $g$, the marked starts are $c-g$ and $c$ modulo seven. The program searches all seven choices of $c$ and all distinct permutations of the three transverse distances. This accounts for permutations of the transverse axes when the distinguished support was normalized.

Each transverse full band gives allowed values of the physical middle on its cut through the two distinguished projections. Both cuts on an axis prescribe the same middle bits wherever they overlap. Having fixed all visible bits, the enumeration tries all subsets of the remaining common sites. On each transverse axis the unmarked levels fit into two adjacent pairs, so at most eight common sites can lie outside all six marked bands. The six reconstructed 33-band projections must agree on all crossings between different axes. The common-level lower bound of 16 is used only for marks at distance one. [Contact enumeration](filter_contacts.cpp) · [Middle assignments](middle_layers.cpp) · [Six-band join](join_bands.cpp)

Each surviving choice specifies an entire physical three-level slab on the distinguished axis. Repeating the same argument with any other adjacent axis as the distinguished axis yields that axis's complete list of potential slabs. To place them in a common coordinate system, normalize the later marked start on every axis to 0. On an axis of gap $g$, the remaining reflection is $x\mapsto1-g-x$, which exchanges the two marked bands. The program uses every relative sign and every axis permutation preserving the distance profile. The slabs must agree on their physical overlaps and their union must be independent. [Physical slab join](join_slabs.cpp)

For every surviving union, each disjoint marked band has a prescribed projection wherever it crosses a fixed slab. The program enumerates every maximum three-dimensional atlas support with that restriction and tests whether every remaining projected word has at least one lift compatible with the fixed union. Supports on different axes must also agree on their planar crossing. [Remaining band check](join_remaining.cpp)

## Replay

From this directory, run the following to check all nine mixed exclusions. For one profile, append `--profiles` and its four-digit name.

```sh
python3 verify_mixed.py
python3 verify_mixed.py --profiles 1113
```

The replay checks every count at each intersection size from 16 to 33. Temporary contact tables, middle choices and surviving slabs are removed when their profile finishes. The all-adjacent proof has its own final exterior check and is replayed with `python3 verify.py`. [Mixed census](mixed-census.tsv) · [Verifier](verify_mixed.py)
