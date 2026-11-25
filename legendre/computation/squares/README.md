# Consecutive-square prime certificates

For every integer m in each of the following four inclusive ranges, the corresponding archive supplies one prime strictly between m² and (m+1)². Each file holds exactly 1,000,000 consecutive certificates.

| File | First m | Last m |
| --- | ---: | ---: |
| low.iw.gz | 70,500,001,100,001 | 70,500,002,100,000 |
| midpoint85.iw.gz | 85,249,999,000,001 | 85,250,000,000,000 |
| target100.iw.gz | 99,999,999,000,001 | 100,000,000,000,000 |
| high.iw.gz | 733,395,927,758,894 | 733,395,928,758,893 |

The included paired archives certify the stronger Oppermann inequalities for every m from 70,500,000,000,001 through 70,500,001,100,000. Combined with the published verification through 70,500,000,000,000, these extend the consecutive-square result through 70,500,002,100,000. The midpoint, target and high files cover three separate ranges above that contiguous prefix. [Sorenson and Webster](https://doi.org/10.1007/s40993-024-00589-4)

## Replay

Run these commands from this directory; they write the binaries `codec` and `verify` here (the three `.cpp` and `.hpp` links point into `../direct`). They read only the files listed in the table and the two Oppermann files, and need no network access. The decoder checks each stream's framing, record count, order, and CRC-32. The separate verifier checks each index, the two strict square inequalities, and the primality certificate. The manifest includes SHA-256 digests of each compressed archive and its decoded canonical decimal stream.

```bash
set -euo pipefail
c++ -O3 -std=c++17 -DPOWER_WITNESS_SQUARES interval_witness_codec.cpp -o codec
c++ -O3 -std=c++17 -DPOWER_WITNESS_SQUARES -DUSE_GMP check_power_witnesses.cpp -lgmpxx -lgmp -o verify
gzip -dc low.iw.gz | ./codec unpack | ./verify 70500001100001 70500002100000
gzip -dc midpoint85.iw.gz | ./codec unpack | ./verify 85249999000001 85250000000000
gzip -dc target100.iw.gz | ./codec unpack | ./verify 99999999000001 100000000000000
gzip -dc high.iw.gz | ./codec unpack | ./verify 733395927758894 733395928758893
python3 check_square_witnesses.py 70500000000001 70500001000000 square_witnesses.gz
python3 check_square_witnesses.py 70500001000001 70500001100000 square_oppermann_extension.gz
```

An alternative build of the verifier omits `-DUSE_GMP` and links `-lcrypto` in place of the GMP libraries. Witness generation on the benchmark machine used the following build.

```bash
c++ -O3 -std=c++17 -DPOWER_WITNESS_SQUARES fast_power_witness.cpp -lgmpxx -lgmp -o search
./search 70500001100001 70500002100000 --witnesses | ./codec pack | gzip -n -9 > regenerated.iw.gz
```

The generator uses AVX-512 IFMA. Adding `-DPOWER_WITNESS_SCALAR` selects its portable scalar arithmetic. Replay requires an ordinary 64-bit C++17 compiler with unsigned 128-bit integer support. The square and 11/5 archive formats have different magic bytes.

## Why the witness is prime

Let p be the odd integer being tested and let F be 2 raised to the ceiling of one third of its bit length. The verifier checks F divides p−1, so p<F³, and checks 3^((p−1)/2) equals −1 modulo p. For every prime divisor s of p the order of 3 modulo s must contain the full power of two in p−1. Thus F divides s−1. A composite p could then have only two prime factors counting multiplicity, of the form 1+Fx and 1+Fy with x,y positive. If x+y≥F, then xy≥x+y−1 and their product is at least 1+F³. Consequently x+y<F. Dividing (p−1)/F by F yields quotient xy and remainder x+y. The discriminant (x+y)²−4xy would be a nonnegative perfect square. The verifier rules this out, or rules out two factors directly using (F+1)²>p.

## Connection to exponent 11/5

For each n in the remaining large band, set m=ceil(n^(11/10)). The gap (n+1)^(11/10)−n^(11/10) exceeds two by the mean value theorem. Therefore the entire open square interval at m lies inside the requested interval at n. The last square base needed for n=32,654,578,787,389 is 733,395,928,758,893, as follows by comparing tenth and eleventh integer powers.

Extending consecutive-square verification from the published endpoint through that high base would require 662,895,928,758,893 cells. This is 23.04 times the 28,770,724,342,938 base count of the earlier 11/5 band. The million-row runs used one pinned virtual CPU on an Intel Xeon Platinum 8573C with GNU C++ 14.2. Search, pack, gzip -9, decompress, unpack and GMP replay took 3.798 and 6.035 CPU seconds per million, respectively, at the low and high endpoints, with wall times of 3.805 and 8.938 seconds. The corresponding archives occupy 855,648 and 872,444 bytes. At those pilot rates a full extension would require approximately 80–127 core-years and 567–578 decimal TB. This is an extrapolation from two short endpoint runs. The manifest records the individual stage timings.

For the shorter proposed extension from the verified prefix through square base 100,000,000,000,000, the midpoint and target samples took 3.845 and 3.908 CPU seconds per million. They occupy 854,144 and 855,230 bytes, respectively. Each decoded exactly to its original canonical decimal text and passed the GMP and OpenSSL replays. Averaging the low, midpoint and target measurements with weights 1:4:1 estimates 3.85 CPU seconds and 854,576 bytes per million, or roughly 3.60 single-core years and 25.2 decimal TB for the 29.5 trillion square cells alone.
