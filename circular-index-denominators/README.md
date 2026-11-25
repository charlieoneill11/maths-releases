# Every denominator occurs in the upper half for the circular chromatic index

**Result.** For every integer q > 2 there is a finite connected regular simple graph G whose circular chromatic index is a fraction with reduced denominator q lying strictly between Δ(G) + 1/2 and Δ(G) + 1. Degrees 6 and 9 suffice. This answers Problem 7 of Mazák and Zrubák, *Circular chromatic index of small graphs* (arXiv:2603.08822), for multigraphs and for simple graphs.

- Paper: [circular-index-denominators.pdf](circular-index-denominators.pdf). The LaTeX source is in [paper/](paper/) and builds with `pdflatex main.tex`, run twice.
- Programs and certificates: [code/](code/).

## The results

- **Multigraphs.** The multigraph (q−1)C<sub>2q+1</sub> has Δ = 2q − 2 and circular chromatic index Δ + 1 − 1/q. This also follows from a 1996 theorem of Gao and Zhu; the paper gives a short direct proof.
- **Degree nine.** Every rational number in [19/2, 29/3] is the circular chromatic index of a connected 9-regular simple graph. Replacing each vertex of a cubic graph H by a hub carrying two copies of a fixed 13-vertex graph Q multiplies the circular chromatic index by three in this range, and Lukoťka and Mazák constructed cubic graphs with every rational circular chromatic index between 3 and 10/3. This gives every denominator q > 2 except 4, 6 and 10, for example 135/14 and 173/18.
- **Degree six.** Rings of three or five 9-vertex blocks give connected 6-regular simple graphs with circular chromatic indices 27/4, 41/6 and 67/10.

The proofs are computer-assisted. The main finite step (the paper's Lemma 11) is an exhaustive search over 221,975 cases about colourings of Q on a grid of 48 slots, carried out by two independently written C++ programs.

## Checking the result

From `code/`, with Python 3.10 or newer and a C++20 compiler:

```sh
# Q, its (19,2)-colouring and the extension lemma (Table 1, Lemma 9)
python3 replay_tripod.py
# Lemma 10: the 21 terminal gap triples, by SAT (needs python-sat) and by an independent search
python3 replay_tripod.py --sat
c++ -std=c++20 -O3 tripod_check.cpp -o tripod-half
python3 replay_tripod.py --emit | ./tripod-half
# Lemma 11: the 221,975 placements, with each of the two checkers, and the positive control
c++ -std=c++20 -O3 tripod_48.cpp -o tripod-48
python3 replay_48.py --checker ./tripod-48 --jobs 4 --cross-check-cases
c++ -std=c++20 -O3 tripod_48_bitsets.cpp -o tripod-48-bitsets
python3 replay_48.py --checker ./tripod-48-bitsets --jobs 4
# Theorem 13 (i): lifting a colouring of a cubic graph, on five grids
python3 transfer_colouring.py
# Section 6: facts (F1)-(F4), the block colourings of Table 2 and the three rings
c++ -std=c++17 -O3 replay_blocks.cpp -o replay-blocks
./replay-blocks
python3 replay_mixed.py
python3 audit_blocks.py          # independent SAT check of (F1)-(F4), needs python-sat
# Theorem 8 for 3 <= q <= 64, and further checks of small cases
python3 verify.py
```

`replay_tripod.py --sat --drat-trim /path/to/drat-trim` also writes and checks a DRAT proof for each of the nineteen unsatisfiable cases of Lemma 10. Each 48-slot checker takes about an hour of processor time, split over the `--jobs` workers; everything else takes at most a few minutes. [code/tripod_receipt.json](code/tripod_receipt.json) records the counts and the SHA-256 hashes of the generated schedule and case files.

## Citing

```bibtex
@misc{circular-index-denominators-2026,
  author       = {O'Neill, Charles and Kirkby, Max and {Astra}},
  title        = {Every denominator occurs in the upper half for the circular chromatic index},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://charlesponeill.com/maths-releases/circular-index-denominators/}},
  note         = {Preprint. Programs and data: \url{https://github.com/charlieoneill11/maths-releases/tree/main/circular-index-denominators}},
}
```
