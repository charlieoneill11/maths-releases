# A necessary axis profile at 112 words

**Every 112-word independent set in four dimensions has an axis with at
most one full 33-word band.** On such an axis either all seven bands have
size 32, or one has size 33, one has size 31 and the other five have size
32. This follows by summing the seven adjacent band sizes to 224.

Suppose instead that there are at least two full bands on every axis.
The transfer of the previous 113-word exclusions forces an axis A with
band sizes \((33,30,33,32,32,32,32)\), up to a dihedral isometry. The
single-level sizes on A are \((18,15,15,18,14,18,14)\). On every remaining
axis there is a pair of full bands whose starts have distance two or
three. Rotating or reflecting A makes its two distinguished starts 0 and 2.
[Arithmetic reduction and transferred hypotheses](../upper113/transfer112.md)

Write \(S,T\) for the 33-point projections of the full A-bands on
levels 0,1 and 2,3. The physical middle levels select 15 points of \(S\)
and 15 points of \(T\). No selected pair is confusable across the two
levels. Consequently, exactly 30 edges in any perfect matching of the
bipartite conflict graph have a chosen endpoint. Three edges have neither.
In a partial assignment we can reject four forced empty edges, or either
middle level already being too large or having fewer than 15 choices left.
These are the only changes to the previous geometric proof. The planar
contact enumeration, six-way join of actual 33-word projections, and
direct-coordinate audit apply with the same inputs and orientation
conventions. [Distance-two proof](README.md) · [Matching test](match_middle.cpp)

| Transverse gap choices | Source pairs after planar filtering | Mark placements | Layouts after matching | Planar-compatible layouts in direct audit | Physically compatible layouts |
|---|---:|---:|---:|---:|---:|
| 2,2,2 | 9,767,343 | 25,578,139 | 615 | 125 | 0 |
| All seven orders containing a 3 | 16,076,232 | 96,313,808 | 9,975 | 0 | 0 |

The six-band joins visit 187,395 and 98,747 compatible prefixes,
respectively. The absence of a compatible product closes all 1,540
four-axis multisets left by the transfer under the assumption of at least
two full bands per axis. The existence of a 112-word packing with an
axis having zero or one full band remains open.

## Replay

From this directory, run the two registered modes. Each regenerates the
full normalized source-pair census from the maximum 33-word atlas and
runs both geometric checks.

```sh
python3 verify.py --target 112 --mode 2222
python3 verify.py --target 112 --mode mixed
```
