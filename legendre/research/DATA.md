# Data files

The program `check_outer_theorem.py` (the optional sharper cutoff in the appendix of the paper) reads three data files in this directory. `check_low_zero_cutoff.py` checks the digest of the zeros file before using it; the other two can be checked with `sha256sum`.

| File | SHA-256 | Contents |
| --- | --- | --- |
| `gap_histogram_4e18.gz` | `7227a85c31cbfc16e4bbd5588d4b3bb1a9c11e360d558745cc55e73b9f5d11b7` (compressed file) | Tomás Oliveira e Silva's table of prime gaps for primes up to 4 × 10¹⁸, unchanged from the copy he distributes. |
| `cofactor_gap_prices.json` | `660e0b6195659f6ed30cc5c9382725b5ae7d70f12bb4702842fa1cd9e2147e28` | The 48 families **c**ᵢ used in the convexity inequality. |
| `platt_low_1400000.delta.gz` | `e5c768ba7975c6c5a0c36de1e53328867b86353ed5188acfe301513764c7ba86` (decompressed bytes) | The first 1,400,000 ordinates of zeros of ζ(s), as computed by David Platt and distributed by the LMFDB. |

## Sources and licences

- **Prime gaps.** T. Oliveira e Silva, S. Herzog and S. Pardi, *Empirical verification of the even Goldbach conjecture and computation of prime gaps up to 4·10¹⁸*, Math. Comp. 83 (2014), 2033–2060, <https://doi.org/10.1090/S0025-5718-2013-02787-1>. Table: <https://sweet.ua.pt/tos/gaps.html>. The file's own header gives its attribution and conventions.
- **Zeta zeros.** D. Platt, *Isolating some non-trivial zeros of zeta*, Math. Comp. 86 (2017), 2449–2467, <https://doi.org/10.1090/S0025-5718-2014-02884-6>. The data come from the LMFDB (<https://www.lmfdb.org/zeros/zeta/>), which distributes them under CC BY-SA 4.0. `platt_low_1400000.delta.gz` adapts them under the same licence. Each ordinate is truncated to an integer number of units of 10⁻¹¹, and the differences between consecutive ordinates, starting from 14 × 10¹¹, are stored as five-byte unsigned little-endian integers. The paper accounts for the error this truncation introduces. `platt_low_1400000.tsv` lists the 14 LMFDB pages the data were taken from, with hashes of the raw responses.
