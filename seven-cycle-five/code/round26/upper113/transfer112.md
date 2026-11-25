# What the full-band proofs imply at size 112

**Every 112-word four-dimensional independent packing has an axis with at
most one full 33-word band.** To prove this, assume instead that every axis
has at least two full bands. The transferred 113-word searches exclude
12,081,245 of the 12,082,785 four-axis profile multisets with this property.
They force one axis of every remaining multiset to have band sizes
$(33,30,33,32,32,32,32)$ up to translation and reflection. The separate
size-112 geometric search excludes all 1,540 remaining multisets.
[Arithmetic checker](transfer112.py) · [Size-112 proof and independent geometric replay](../nonadjacent113/target112.md)

For an axis let $d_i$ be 33 minus the size of the band on levels $i,i+1$. At size 112 the seven deficits sum to seven, and the layer sizes are $h_i=13+d_{i+1}+d_{i+3}+d_{i+5}$, with indices modulo seven. The 1,716 labelled nonnegative deficit vectors have 133 classes under translations and reflections. The following tests take the first applicable row.

| Property of the axis | Classes | Labelled vectors |
|---|---:|---:|
| Zero or one full band | 4 | 43 |
| Adjacent full bands with a shared level of size 16 through 19 | 86 | 1,141 |
| A full pair at distance two whose middle band has at least 31 sites and whose two middle levels each have 14 through 19 sites | 23 | 301 |
| A pair of full bands at distance three | 19 | 224 |
| Two full bands separated by a size-30 middle band | 1 | 7 |

The one-axis checker also verifies that every axis with at least two full bands offers either an adjacent pair meeting the second row or a disjoint pair. On four such axes, the presence of a second-row axis lets us use its three-level slab as the distinguished source. Choose an admissible adjacent pair or a disjoint pair on every other axis. The nine mixed proofs rule out their marked patterns under these hypotheses alone. If all four pairs are adjacent, the independent exterior bound is 105. [Mixed proofs](mixed.md) · [All-adjacent proof](README.md)

If there is no such adjacent source, all four axes offer disjoint pairs. An axis in the third row supplies the size requirements in the distance-two matching test. Its middle levels use at least 31 endpoints of a 33-edge perfect matching and each contributes 14 through 19 words. The transverse axes need only supply their two disjoint full bands. If all four axes have a distance-three pair, the eight-band planar agreement test applies without a total-size assumption. [Distance-two source](../nonadjacent113/README.md) · [Distance-three proof](gap-three.md)

Thus a remaining multiset with two full bands per axis consists of the last 20 classes, and contains the unique last-row class at least once. Its normal form is $d=(0,3,0,1,1,1,1)$, giving layer sizes $(18,15,15,18,14,18,14)$. Removing one copy of that class leaves a multiset of three items from 20, giving $\binom{22}{3}=1,540$ possibilities. Allowing axes with zero or one full band leaves 1,552,585 of the original 13,633,830 four-axis multisets after this transfer. These counts describe the intermediate arithmetic reduction. In the size-112
run, the two middle levels pick 15 points each, leaving three unused edges of
a perfect matching between the distinguished 33-word projections. The
geometric checker tests all 10,590 layouts that survive this matching test
and finds no compatible set of six transverse projections. Therefore the
remaining 1,540 multisets with two full bands on every axis are excluded.
[Matching and projection replay](../nonadjacent113/target112.md)

The four classes with fewer than two full bands are explicit. Either all seven bands have size 32 and all levels have size 16, or one band has size 33, one has size 31, and the other five have size 32. In the latter case the circular distance between the distinguished band starts is 1, 2 or 3. Every layer on such an axis has size 15, 16 or 17.

```sh
python3 transfer112.py
```
