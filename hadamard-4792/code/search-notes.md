# Search for the order-4792 witness

These records trace the search from the order-5912 control through the order-4792 quotient investigations. The completed construction, including the winning case and verification commands, is in the [result](README.md).

## Reproducing the order-5912 control

Kishan Kumar supplies the witness. From a checkout of vatskishan03/Hadamard at `d885022144ba6bf4efa8315e14871a3736947527`, run the commands below with Python 3, NumPy, SciPy, SymPy and GCC on x86-64 with AVX2. The variable `research` points to this folder. The independent checker itself requires only Python 3.10+ and NumPy.

```sh
cd search/eightp/gs
gcc -O3 -march=haswell -shared -fPIC -o libgl1.so gl1.c -lm
for ps in 32 64 128; do gcc -O3 -march=haswell -DPS=$ps -o gl2_$ps gl2.c -lm; done
mkdir -p runs tmp out work
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python3 repro_5912.py --fast --no-build
python3 ../check/odd_spence_cert.py ../../../hadamard/5912/certificate.json
python3 "$research/gram.py" ../../../hadamard/5912/certificate.json 5912
```

Round 33 of base seed 1002 reproduced 2,000 first-stage instances and 987 distinct instances under the upstream reversal filter. The recorded solution occurred at index 341. Its four sign sequences match the certificate. Their sums are all 1 and total PAF is 5908 at zero and −4 at the other 1476 shifts. The independent entry-formula build checked all 17,472,916 unordered distinct row pairs by integer Hamming distances. Its CSV SHA-256 is `b4846b8e76f059552a232a4a6d0f815022c3b178d9103d044965894b6f9c4aa6`. [Upstream control](https://github.com/vatskishan03/Hadamard/tree/d885022144ba6bf4efa8315e14871a3736947527/hadamard/5912)

## Two quotients of the order-4792 problem

Use the simultaneous multiplier (2,4) on K = Z/7 × Z/19, of order nine, and the four nonzero squares on the additive field F₉. Each field sheet is described by 17 signs. For either retained prime p, compress over the other prime. The three compressed rows correspond to zero, squares and nonsquares in Z/p. Their three columns correspond to the same classes in F₉. The normalized block sum is +1. On F₉ the three Fourier values of a row (a,b,c) are a+4b+4c, a+b−2c and a−2b+c. On Z/p a real triple (z,a,b) has trivial value z+(p−1)(a+b)/2 and nontrivial squared modulus ((2z−a−b)²+p(a−b)²)/4. These follow by summing the quadratic periods on each field. Every nontrivial character must have combined squared modulus 4792.

The p=7 enumeration gives 6,210 candidate blocks up to inversion after the single-block power bounds, and p=19 gives 2,738. Both yield 59 ordered pairs of F₉ nontrivial Fourier values and 37 candidate four-block F₉ patterns up to block permutations. The latter count imposes the field equations and single-block bounds. Combining the prime-quotient equations is a further test. The sampler keeps a representative per identical signature and samples compatible projections. This sampling can omit valid nodes.

For an independent check of the stored projections, `lift.py` expands the twelve orbit masks directly over Z/7 × Z/19 × Z/3 × Z/3. These particular signs realize the stored margins. It checks the summed integer autocorrelation of each compressed quadruple at all 63 and 171 shifts. For kernel size k this must equal 4792−4k at zero and −4k elsewhere.

```sh
python3 quotient.py 7
python3 quotient.py 19
python3 joint.py --seed 4792 --rounds 220
python3 joint.py --seed 479203 --rounds 6000
python3 lift.py node-a.json
python3 lift.py node-b.json
python3 complete_node.py node-a.json
```

| Fixed projections | Individual block lift counts | Quadruples passing the defect identity | Full lifts |
| --- | --- | ---: | ---: |
| A | 207507, 120717, 41067, 492804 | 182866572115344 | 0 |
| B | 175158, 92313, 22491, 53703 | 0 | 0 |

Each sheet fibre is enumerated over all 131,072 possible masks. The defect cost is 10 where all three sheet signs agree, 6 where the two nonzero sheets agree but oppose the zero sheet, and 0 otherwise. Its sum over four blocks must be 528. Indeed the square of the field-trivial compression a+4b+4c is respectively 81, 49 or 1. The required sum of squares is 4792−36 = 4756, giving (4756−4·133)/8 = 528. Node B has minimum total cost 600. Node A has ten feasible ordered cost tuples. For each, the checker hashes the three channels’ integral PAF vectors at the six mixed shift representatives into the additive group modulo 2⁶⁴, and compares every complementary pair. A full lift necessarily matches even after this reduction. The run found zero hash matches. The two exclusions concern these literal margins in the given orientation.

## Three simultaneous projections

The four sign blocks in `three-projections.json` simultaneously satisfy the complete projected PAF identities on Z/7 × Z/19, Z/7 × F₉ and Z/19 × F₉. This realizes all 333 characters of the full group which are trivial on at least one factor, including the trivial character. There are 864 characters left. In the full group 972 **shifts** have incorrect PAF. Character counts and shift counts measure different conditions.

The search first solves the compressed field-trivial channel on Z/7 × Z/19. On each K-orbit, write the three signs as (s+e,e+t,e−t). Once s and e are fixed, t is zero on defects and free in {±1} on the remaining orbits. Both nontrivial F₉ Fourier values are s±3t. The program exhausts the remaining sign choices per block, groups them by projected power values, and matches four blocks on the two trivial-frequency powers and four mixed powers of the two prime quotients. One representative per power vector suffices to produce a projected witness. This compression loses information required for a full lift.

Seed 479204, round 7, local instance 2 produced the stored example after testing 24 within-round representatives. Run from this directory, with `gs` set to the absolute path of the pinned and built upstream `search/eightp/gs`.

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 GS_EXACT_CAP=1200 python3 three_quotients.py "$gs" --rounds 8 --output /tmp/three-projections.json
python3 audit_projections.py three-projections.json
```

The audit uses only the Python standard library. It reconstructs the multiplier orbits and translates the signs directly over all quotient shifts and all 1197 original shifts. Its `--require-full` option exits with a failure on this sample.

## Measured upstream search

The first pilot used the same upstream build as the control. It sampled eight of the 1,032 feasible allocations in the (2,4) shape. It returned 12 first-stage instances in 1,066 rounds, with three passing the second-stage row filter and zero completed matrices. The recorded joins visited 5,136,769,514 list pairs in 103.41 CPU seconds. The whole process took 151.65 CPU seconds, including setup. The pilot was time limited, so round counts can vary by machine. The published 1,500 core-hour figure is a search estimate. This pilot measures throughput and does not calibrate a hit probability. [Kumar’s §§107–108](https://github.com/vatskishan03/Hadamard/blob/d885022144ba6bf4efa8315e14871a3736947527/search/NOTES.md)

```sh
# From Kumar's search/eightp/gs after building as above
GS_EXACT_CAP=1000 GS_MAXINST=30 python3 prod_tau.py spence '[7,19]' 9 '[[[2,4],1]]' 150 479201 runs/479201 250 12000 8
```

## Public construction and proof records

- Table 5 includes 599 in its 8p row. At the time of the source audit, the Hadamard Matrix Explorer listed 4792 and 5752 as unknown. Kumar credits the 5912 construction to his Spence search. [Egan–Kotsireas–London–Ó Catháin](https://arxiv.org/abs/2610.27175v2) · [Explorer](https://www.math74.com/Hadamard/unknown.html) · [Kumar’s account](https://generalised.si/research/hadamard-matrices) · [Frontier](https://github.com/vatskishan03/Hadamard/blob/d885022144ba6bf4efa8315e14871a3736947527/FRONTIER.md)
- Checked the November 20–25 GitHub release, commit and issue/PR feeds of OpenAI/math, both specified branches of solved-conjectures, and Kumar’s repository. The OpenAI main feed returned four commits, including the November 24 manuscripts merged on November 25. None of the three repositories had a GitHub release listed. Family 179 classifies matrices of the form Hᵢⱼ = h(j−i). Family 266 has hypotheses on complex 6×6 matrices. Neither gives an exclusion for the bordered order-4792 problem. At this order circulant nonexistence also follows immediately since the squared common row sum would have to equal 4792. [OpenAI update](https://github.com/openai/math/commit/3344da5999) · [Family 179](https://github.com/openai/math/blob/3344da59/lean/docs/179.md) · [Family 266](https://github.com/openai/math/blob/3344da59/lean/docs/266.md)
- The solved-conjectures project supplies a conditional border, an automorphism restriction and multiplier restrictions at 2396, which could give 4792 by doubling if a 2396 witness is found. The order-479 automorphism obstruction is specific to 2396. Its research branch also studies an obstruction to quaternionic composition. The relevant issue threads and the two branches contain no 4792 certificate located in this audit. [Partial results](https://github.com/1337isnot1337/solved-conjectures/tree/d704b57700/results/hadamard-2396) · [Research branch](https://github.com/1337isnot1337/solved-conjectures/tree/31df82431b/research/hadamard-conjecture) · [Issue 340](https://github.com/1337isnot1337/solved-conjectures/issues/340)
- The November construction account treats twelve orders under 2000. Its compression and power-spectrum checks apply to our projected searches. Its even-index q border with |G|=1198−(q−1) would require q to divide 1199, which is odd. On November 23 Kotsireas, Liu and Winterhof posted a construction of Butson matrices from prime-ary Legendre pairs and ternary witnesses through length 32. These give a different alphabet and size. [Twelve-order construction, §§1 and 4](https://hexagonmath.org/pdf/2611.00637v1) · [November 23 preprint](https://arxiv.org/abs/2611.31067)
- Other possible routes include a quaternary matrix of order 598 as input to Miyamoto, or a suitable dihedral complementary pair of length 23, since 599=26·23+1. Kumar reports that the restricted real-first palindrome search at length 23 was empty. [Quaternary database](https://www.cs.uleth.ca/~zaitsevv/quaternary.html) · [Kumar’s §102–107 investigations](https://github.com/vatskishan03/Hadamard/blob/d885022144ba6bf4efa8315e14871a3736947527/search/NOTES.md)

The source audit is bounded by the visible records on November 25, 2026. All computations here used local CPU. No external inference was run and no additional compute was purchased.

## Allocation census and exact lifts

Write a single block specification as (n,m,σ,ε). Here n is the number of defective K positions, m counts the defects with s=−2e, and σ, ε are the sums of s and e. One four-block allocation fixes the four pairs (n,m). Each allocation can admit several normalized row-sum specifications. Kumar's enumeration yields 1,032 allocations. Expanding its exact row-sum states, normalizing independent block signs, and sorting the block specifications gives 1,141 cases. There are 220 distinct single-block specifications.

The independent prime-quotient screen retains 524 cases with 1,364 ordered choices of the four t-sums, modulo simultaneous sign reversal. For each of the 220 specifications it enumerates the three signs in a compressed fibre, tracking (n,m) exactly. It combines the three multiplicative cosets of the retained prime and requires flat power at both nontrivial field characters and all mixed characters of that quotient. A common t-sum four-tuple must work for both prime quotients. A surviving case can still fail the mixed K shifts. The projected weights are identical for the multipliers (2,4) and (2,5).

In a second upstream pilot, seed 479202 and allocation (4.1,7.4,12.3,33.0) produced 5,252 first-stage instances in 451 rounds and 601.80 CPU seconds. Of these, 2,268 failed the row filter and 2,984 passed it. The joins visited 48,335,067,546 list pairs. Many sampled instances are equivalent. An exact enumeration reduced the three normalized row patterns of this allocation to 24, 8 and 10 first-stage representatives, respectively. Only the 24-instance pattern passes the phase row-sum filter. None of the 42 lifts to a full matrix. Here “representative” counts rows remaining after the stated reductions; some may still be equivalent.

The first enumeration uses Kumar's explicit single-block lists and C join. It keeps a lexicographically minimal first block under all common scalar multipliers on K, and it can independently invert each of the other three blocks. The field-trivial values in {±1,±7,±9} uniquely recover both s and e. A separate join partitions by the two axial power sums and checks six integral mixed-shift coordinates. The two implementations give identical lists for the 24-instance pattern. All 42 instances also passed through Kumar's second-stage binary with floating-point PSD rejection disabled. The native phase checker hashes integral correlations only, retains all equal keys, and directly checks the three full K-channel identities on any hit.

Two allocations have the largest estimated completion fraction among the positive-estimate allocations in the upstream token model. Both use defect weights (6,18,18,18) and σ=1, ε=0 in each block. Both fail the paired prime-quotient screen. The independent K-first searches return 13,708 first-stage representatives for opposed-defect counts (0,0,0,18) and 44,764 for (0,0,9,9). The native phase checker found zero compatible projected classes in both lists.

Set `gs` and `research` as above. The commands below work in a separate scratch directory. The native joins require a C++17 compiler. The catalogue order is deterministic for the pinned input.

```sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
c++ -std=c++17 -O3 -shared -fPIC "$research/pair_join.cpp" -o pair_join.so
c++ -std=c++17 -O3 -shared -fPIC "$research/phase.cpp" -o phase.so
gcc -O3 -march=haswell -DPS=32 -DNEARMISS -o "$gs/gl2n_32" "$gs/gl2.c" -lm
python3 "$research/catalogue.py" "$gs" bands.json
python3 "$research/screen.py" bands.json survivors.json
python3 "$research/band.py" "$gs" a.npz
python3 "$research/finish_band.py" "$gs" a.npz --output hit.json
python3 "$research/coarse_band.py" "$gs" high.npz --library pair_join.so
python3 "$research/phase.py" phase.so high.npz --output hit.json
python3 "$research/coarse_band.py" "$gs" high2.npz --library pair_join.so --spec '6,0,1,0:18,0,1,0:18,9,1,0:18,9,1,0'
python3 "$research/phase.py" phase.so high2.npz --output hit.json
python3 "$research/conditioned.py" "$gs" survivors.json a-conditioned.npz pair_join.so --index 308
python3 "$research/phase.py" phase.so a-conditioned.npz --output hit.json
```

The conditioned join additionally tracks the local field-trivial sum, s-sum, defect count and opposed-defect count on each retained prime coset. For case 308 it reduces the 24 K-level candidates to four while retaining all 19 projected class matches of the separate phase search.

## Independent census, exact search and checkpoint

The independent C++ enumeration starts from the eight possible triples of signs, assigns the three light positions of weights 1, 3 and 3, and enumerates multinomial counts on the fourteen positions of weight 9. After four-block matching on the defect and two field-power equations it produces the same 1,141 normalized specifications. The following check compares the sets element by element.

```sh
c++ -std=c++17 -O3 "$research/audit_census.cpp" -o audit-census
./audit-census > audit-bands.txt
python3 - <<'PY'
import json
from pathlib import Path
expected = {tuple(x for block in sorted(b["spec"]) for x in block)
            for b in json.loads(Path("bands.json").read_text())}
observed = {tuple(map(int, line.split())) for line in Path("audit-bands.txt").read_text().splitlines()}
assert expected == observed and len(expected) == 1141
PY
c++ -std=c++17 -O3 -shared -fPIC "$research/margin_blocks.cpp" -o margins.so
python3 "$research/phase_control.py" phase.so "$research/three-projections.json"
python3 "$research/conditioned.py" "$gs" survivors.json a-margin.npz pair_join.so --index 308 --margin-library margins.so
python3 "$research/phase.py" phase.so a-margin.npz --output hit.json
python3 "$research/campaign.py" "$gs" survivors.json pair_join.so phase.so work --margin-library margins.so --generator 4 --max-list 123002880
```

The margin-based implementation enumerates each set of seven heavy positions in 279,936 words. It matches the two sets and the three light positions against both prime margins. Case 0 has an unfiltered single-block list of 83,603,520. The margins retain 262,638 representatives for that block, and the four-block join finds zero K-level instances after 100,808,352 pair entries. Both implementations return the same four literal K-level instances for case 308. As a positive control, a separate Python calculation obtains the full correlation fingerprint of the stored three-projection example. The native phase join reaches its direct verifier once for that fingerprint. The verifier rejects the example on the original identities.

The pre-discovery checkpoint contains 237 completed cases, 166 for generator (2,4) and 71 for (2,5). The runs covered 242,686 first-stage instances and 8,523,552 matches of projected power classes. Each search finished without a lift. Each line contains the exact specification, generator, input fingerprint and search counters. To rerun the saved cases from scratch, use an empty work directory. To continue from existing records, first run the command below. Workers can partition the indices with `--shards N --shard J`, where J runs from 0 to N−1. The other generator uses `--generator 5`.

```sh
python3 "$research/checkpoint.py" restore survivors.json work "$research/campaign-progress.jsonl"
```

## Dihedral pairs of length 23

A length-23 dihedral Golay pair over {±1, ±i, ±s} would give order 4792. Multiply by a binary Golay pair of length 26, append one real entry using a Golay pair of length 1, then apply Theorem 7 and the signed-group doubling lemma. The order is 8(26·23+1). Kumar searched an ansatz with one entirely real sequence. [Kamali and Kharaghani, Lemmas 1 and 3 and Theorem 7](https://ajc.maths.uq.edu.au/pdf/18/ocr-ajc-v18-p139.pdf) · [Kumar’s dihedral search](https://github.com/vatskishan03/Hadamard/blob/d885022144ba6bf4efa8315e14871a3736947527/search/NOTES.md)

Here W = i + s Σ c_d(z⁻ᵈ−zᵈ), with c_d in {±1}. Take A = R + P W and B = S + Q W, where P = zᵖ and Q = zᑫ(1 ± zʲ). The two translated copies in B have disjoint supports. R and S contain real signs on every uncovered position in the interval from 0 through 22. Since W* = −W, all four polynomials A, B, A*, B* commute. Their norm sum is scalar precisely when RP* + SQ* is invariant under z ↦ z⁻¹. Its scalar part is the sum of the ordinary aperiodic autocorrelations of the real, imaginary and reflection coordinates. The implementation hashes both equations at every lag and checks any collision directly. At z = 1 and z = −1 the reflection coordinate vanishes. The real-coordinate magnitudes must be respectively 4 and 5 when |Q| = 2, or 6 and 3 when Q = 0. This rejects five or more offset pairs because B has at most one real position.

```sh
c++ -std=c++17 -O3 "$research/dihedral23.cpp" -o dihedral23
for n in 1 2 3 4; do ./dihedral23 "$n"; done
```

| Offset pairs | B templates | A entries | B probes | Matching fingerprints |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 1,386 | 9,484,090 | 10,300,872 | 0 |
| 2 | 3,820 | 14,513,460 | 1,745,768 | 0 |
| 3 | 4,896 | 14,532,000 | 118,304 | 0 |
| 4 | 2,400 | 9,913,856 | 1,184 | 0 |

This stage excluded the displayed length-23 templates. The larger dihedral enumeration followed.

## Complete length-23 dihedral input check

The full six-letter length-23 dihedral input is excluded by the polynomial reductions and reproducible exhaustive searches in the [length-23 report](dihedral-23.md). The source constructions and earlier partial searches are credited there. Two independent support enumerations agree on the literal set of 1,487,333 mixed support pairs. Fifteen pass the modulo-4 sign equations. An independent 2×2 integer matrix audit rejects all 3,168 sign assignments. The wholly real case reduces to Kumar’s positive-palindrome search and also fails a separate exact enumeration. Bright et al. previously resolved the purely complex case. The subsequent Spence search produced the [order-4792 witness](README.md).

An exact optimization now combines repeated K-level joins. When three row lists coincide, the fourth lists can be replaced by their union. Case 515 drops from 5,502,236,736 pair entries to 1,095,156,560 and returns the same 5,008 literal K-level quadruples as the original implementation. Case 223 drops from 31,026,296,806 pair entries to 1,545,659,863 and recovers the same count of 3,675. Use `--no-combine` with `conditioned.py` to reproduce the original joins.

On November 25, the subsequent public updates through solved-conjectures main commit `f087ed90e86a` concerned interval rank unimodality and the Sobolewski–Ulas obstruction. The research branch and OpenAI/math heads remained at `31df82431b` and `3344da5999`. [Compared changes](https://github.com/1337isnot1337/solved-conjectures/compare/541ef05841df...f087ed90e86a)

## Larger scalar symmetries

All 24 scalar subgroups on K having at most 16 point orbits are excluded when paired independently with either the field-squares subgroup or the two independent sign flips of the field coordinates. The successful order-4792 construction uses a 17-orbit subgroup. The [proof and audit](scalar-products.md) include exhaustive subgroup generation, integral spectral bounds, exact four-block joins and commands. The [machine-readable results](scalar-product-results.json) record each of the 16 inclusion-minimal subgroups.

The same integral Rayleigh bound now screens the original K-level blocks before joining. It keeps 8,382 of 51,252 blocks in the largest pool for case 308. With this screen and combined joins, case 223 requires 1,091,073,890 pair entries and returns the same 3,675 literal K-level instances. Its phase search returns 88,098 row-sum tuples and 292,358 projected class matches when all literal instances are retained. Independent scalar, sign, reversal and block permutation reductions identify 3,604 representatives in that case. In case 522 the same reductions take 31,920 instances to 5,291. Use `--no-rayleigh` or `--no-canonical` for the respective comparisons. The phase solver derives possible t-sum tuples once per ordered s-sum tuple from their exact quadratic and linear equations.

The November 25 source refresh through solved-conjectures commit `a51917c3fccb` added work on Sobolewski–Ulas and Frankl. The September computer search for quaternary Legendre pairs produced lengths 42, 46, 52, 58, 66, 72 and 80. Its construction is relevant to a possible length-298 input. For the two Jedwab–Pender families, neither 597 = 3·199 nor 297 = 27·11 is a prime power. The compressed template requiring 297 to be a sum of two squares also fails. [Source refresh](https://github.com/1337isnot1337/solved-conjectures/compare/f087ed90e86a...a51917c3fccb) · [September preprint](https://arxiv.org/abs/2609.04589) · [Kotsireas–Koutschan–Winterhof](https://www.ricam.oeaw.ac.at/files/reports/24/rep24-10.pdf)

## Successful lifts on November 25

Case 268 for the multiplier (2,4) produced the primary [certificate](certificate.json). Its permitted phase-sum tuple was (3,−3,0,0). The conditioned join reduced 5,481,486 raw pair entries to 2,518,683. It found six literal K-level instances, three after scalar, reversal, sign and permutation reductions. Phase record 3 gave the full witness. A clean recompilation of all three native libraries and replay of this case reproduced the same four sign strings. The [search record](winning-case.json) reports 2.83 wall seconds for this case.

A concurrent worker also recorded a hit in case 523. The conditioned join there used 148,622,631,302 pair entries and found 81,210 literal K-level instances. Phase record 53,430 produced a second [certificate](certificate-case523.json). Its recorded case time was 3,664.69 wall seconds. The two case times exclude quotient enumeration and previous search cases. The final worker records contained 250 negative cases for (2,4), 80 negative cases for (2,5) and the two hits for (2,4). Equivalence of the two resulting matrices under signed row and column permutations was not tested.

From a clean scratch directory with the upstream dependencies and build described above, set `research` to this folder and `gs` to the absolute path of Kumar’s pinned `search/eightp/gs` directory. The following commands reconstruct the primary witness. Replacing index 268 by 523 selects the second case.

```sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
c++ -std=c++17 -O3 -shared -fPIC "$research/pair_join.cpp" -o pair.so
c++ -std=c++17 -O3 -shared -fPIC "$research/margin_blocks.cpp" -o margin.so
c++ -std=c++17 -O3 -shared -fPIC "$research/phase.cpp" -o phase.so
python3 "$research/catalogue.py" "$gs" bands.json
python3 "$research/screen.py" bands.json survivors.json
python3 "$research/conditioned.py" "$gs" survivors.json rows.npz pair.so --index 268 --generator 4 --margin-library margin.so
python3 "$research/phase.py" phase.so rows.npz --output candidate.json
python3 "$research/verify_differences.py" candidate.json --check-masks
```

For case 523, omit `--check-masks`, which compares against the printed case-268 masks.

The final November 25 GitHub history check reached solved-conjectures main `fb72bb7731d0`. The two additional commits verify estimates for Lassalle’s conjecture. The checked research, OpenAI/math and Kumar heads remained `31df82431bf2`, `3344da59991e` and `d885022144ba`. The author pages, dated preprint search, Explorer, and public repositories reviewed here yielded no earlier order-4792 witness. [Latest compared commits](https://github.com/1337isnot1337/solved-conjectures/compare/a51917c3fccb...fb72bb7731d0) · [Egan’s publications](https://sites.google.com/site/eganronan/home/publications) · [Kotsireas’s Laurier profile](https://www.wlu.ca/academics/faculties/faculty-of-science/faculty-profiles/ilias-s-kotsireas/index.html) · [London’s Loyola profile](https://www.luc.edu/math/profiles/londonstephen.shtml) · [Ó Catháin’s publications](https://sites.google.com/site/pocathain/publications)

We also retrieved the linked Lean comparator statements for OpenAI families 179 and 266 and the exact Fourier certificate paper. Family 179 requires the whole matrix to be circulant. The family-266 certificate concerns six-dimensional complex row or column ratios. At order 4792 the quotient tests use the characters of the actual additive group, and the final certificate can be verified directly by integer differences. The CRT-specific upstream checker used in the 5912 control requires pairwise coprime coordinate moduli. For the two repeated factors of order three we used the general upstream builder and separately checked the literal matrix. [Circulant comparator](https://github.com/openai/math/blob/3344da59/lean/ComparatorChallenges/CirculantHadamard.lean) · [Order-six paper and comparators](https://github.com/openai/math/blob/3344da59/lean/docs/266.md) · [General Spence builder](https://github.com/vatskishan03/Hadamard/blob/d885022144ba6bf4efa8315e14871a3736947527/verify/verify.py)
