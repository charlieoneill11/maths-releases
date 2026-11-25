# Zero-error codes for the seven-cycle

**Result.** α(C₇^⊠4) ≤ 112 and α(C₇^⊠5) ≤ 392: a zero-error code for the seven-cycle has at most 112 words of length four and at most 392 words of length five. The previous bounds were 115 and 401.

- Paper: [seven-cycle-five.pdf](seven-cycle-five.pdf). The LaTeX source is in [paper/](paper/) and builds with `pdflatex main.tex`, run twice.
- Programs: [code/](code/). The section "The computations" of the paper describes them.
- Formal proof: [lean/](lean/). Both bounds are proved in Lean 4 with Mathlib; see "Formal proof in Lean" below and the paper's section "Formal verification in Lean".

## Formal proof in Lean

The folder [lean/](lean/) holds a Lean 4 development. It proves

```lean
theorem card_le_112 (C : Finset (Word 4)) (hC : IsCode C) : C.card ≤ 112
theorem card_le_392 (C : Finset (Word 5)) (hC : IsCode C) : C.card ≤ 392
```

These are stated in [lean/SevenCycle/Statement.lean](lean/SevenCycle/Statement.lean), where `Word n` is `Fin n → ZMod 7` and `IsCode` says that no two words are confusable.

- **Pins.** Lean v4.29.1 and Mathlib v4.29.1, pinned in `lean-toolchain` and `lake-manifest.json`.
- **Exhaustive searches.** Each search is a Boolean checker written in Lean, with a Lean proof that a successful run excludes the case it covers. It is evaluated with `native_decide`.
- **What you trust.** Both bounds depend on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). They also depend on 197 compiler-generated axioms, one for each named check, stating that the check evaluates to `true`. So you trust the Lean kernel, plus the Lean compiler for those 197 evaluations.
- **Search counts.** The C++ and Python programs in `code/` are used only for regression comparisons and search hints. The formal searches reproduce the paper's counts.

To replay, from `lean/`:

```sh
lake build
lake env lean scripts/axioms.lean > axioms.log
python3 scripts/check_axioms.py axioms.log
```

`check_axioms.py` fails if:
- any declaration depends on an axiom outside that list;
- a `native_decide` proof concludes anything other than `b = true`;
- `sorry`, `admit`, `axiom`, `implemented_by` or `extern` appears in the sources.

The native checks take about four CPU-hours in total, and the largest uses about 4.7 GB of memory. `SEVEN_CYCLE_JOBS=1` forces a serial build.

[lean/REPORT.md](lean/REPORT.md) gives:
- per-check times;
- the full axiom printout;
- the correspondence between Lean results and the paper's lemmas, also in [lean/BLUEPRINT.md](lean/BLUEPRINT.md).

REPORT.md was written in the development repository, so its links to a pull request and to a CI workflow do not resolve here. Its "105–112" range refers only to the 105-word witness that the formal development checks. The best known code has 108 words.

## Replaying the proof

You need `g++` with C++17 and Python 3.10 or later (`upper113/exterior.py` uses `int.bit_count`). No other libraries are used. The replay used a machine with 15 GB of memory.

```sh
cd code/round26
python3 -B verify_upper_bound.py              # all six parts, about 21 minutes
python3 -B verify_upper_bound.py --part P     # one part
```

Here `P` is `atlas`, `four-adjacent`, `mixed-adjacent`, `gap-two`, `mixed-gap-two` or `gap-three`. Before every part the driver checks that `atlas.tsv` has SHA-256 `aee14d35…172e38a`. The `atlas` part regenerates this list of 33-word codes with `round25/multiplicities/atlas/atlas.cpp` and compares it byte for byte with `atlas.tsv`. The other parts run the searches in `upper113/` and `nonadjacent113/`. The driver stops if any assertion fails or any count differs from its recorded value. On one core of a 2.1 GHz Xeon the parts took 7 s, 1 min 50 s, 10 min 38 s, 2 min 8 s, 3 min 17 s and 2 min 49 s, and no part used more than 1.3 GB of memory.

## The second atlas

`code/second-atlas/` holds the enumeration of the 33-word codes described in the proof of Theorem 7 of the paper. Its list of classes is compared with the list `round25/multiplicities/atlas/atlas.tsv` that the searches read:

```sh
cd code/second-atlas
g++ -O3 -std=c++17 -fopenmp atlas3.cpp -o atlas3 && ./atlas3 4   # writes codes33.bin (800 MB)
g++ -O3 -std=c++17 classes3.cpp -o classes3 && ./classes3        # writes classes33.txt
python3 compare_atlases.py classes33.txt ../round25/multiplicities/atlas/atlas.tsv   # needs NumPy
```

`./atlas3 0` and `./atlas3 2` find no codes of sizes 35 and 34. On four cores of a 2.1 GHz Xeon `./atlas3 4` took 21 minutes and 2.4 GB of memory (`-fopenmp` is optional; without it the enumeration runs on one core), and `./classes3` took 31 seconds. The rebuilt `codes33.bin` has SHA-256 `e8833a41…dc12ed8f`, and the rebuilt `classes33.txt` is identical byte for byte to the included file (SHA-256 `af27c750…e9811991`), which `./classes3` overwrites. With the included file the last command can be run on its own (about 2 minutes). It prints

```
classes A 1016 classes B 1016 equal sets: True
sum of recorded orbit sizes (A): 16672544
orbit sizes agree class by class; stabiliser orders {1: 1011, 2: 1, 3: 3, 6: 1}
```

and stops with an error unless the two lists define the same 1,016 classes, the orbit sizes recorded in `classes33.txt` agree class by class with the numbers of distinct images of the representatives in `atlas.tsv`, and these sizes add up to 16,672,544.

## Independent check of the distance-three case

`code/round26/upper113/gap_three_check.cpp` repeats the search of Section 7 from explicit coordinates, without the index used by `gap_three.cpp`, and is run separately from the driver:

```sh
cd code/round26/upper113
g++ -O3 -std=c++17 gap_three_check.cpp -o gap_three_check
./gap_three_check ../../round25/multiplicities/atlas/atlas.tsv
```

The recorded run, compiled with `-march=native` added, took about 25 minutes on one core and 1.1 GB of memory. It ends with `Summary: 348488 choices of S, 143566 with no T, 204922 with some T, 21378687 distinct pairs (S,T), 0 admitting six projections with agreeing crossings`, and its counts for each atlas class of S agree with the cumulative counts printed by `gap_three.cpp`.

## Citing

BibTeX (also in [CITATION.bib](CITATION.bib) and on the [paper's page](https://charlesponeill.com/maths-releases/seven-cycle-five/)):

```bibtex
@misc{seven-cycle-five-2026,
  author       = {O'Neill, Charles and Kirkby, Max and {Astra} and {Fable}},
  title        = {The fourth strong power of the seven-cycle has independence number at most {$112$}},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://charlesponeill.com/maths-releases/seven-cycle-five/}},
  note         = {Preprint. Programs and data: \url{https://github.com/charlieoneill11/maths-releases/tree/main/seven-cycle-five}},
}
```
