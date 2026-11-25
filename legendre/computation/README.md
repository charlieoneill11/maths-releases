# Finite prime certificates for exponent 11/5 and consecutive squares

The November 2026 combined run certified a prime with $n^{11}<p^5<(n+1)^{11}$ at every positive integer $n<35{,}000{,}000{,}000{,}000$ and a prime in $(m^2,(m+1)^2)$ at every positive integer $m\le 10^{14}$. Both finite results rest on certificates checked by integer arithmetic alone; they do not use RH. The run's 51.69 TB archive is in a private bucket, so most of these certificates cannot be checked from this directory. [What the public files establish](#what-the-public-files-establish) separates the two. The all-integer $11/5$ result also needs the analytic argument of the paper, which uses the Riemann hypothesis, now proved by Alpöge. [Coverage ledger](COVERAGE.md) · [Production results and replay](cloud/baseten_prime_pilot/README.md#completed-production-run) · Analytic argument

## Replay the evidence

From this directory on Linux, use Bash, Python 3.8+, gzip, sha256sum, and a 64-bit C++17 compiler with unsigned 128-bit integer support and GMP development headers/libraries. The replay requires no cloud account, GPU, network, or AVX-512 instructions.

```bash
sha256sum -c evidence.sha256
bash replay.sh
```

The script rebuilds the decoders and GMP verifiers in a temporary directory. The ten-million-base continuation extends the public power prefix through **3,883,865,444,451**, and a separate pilot certifies the last million bases below **35,000,000,000,000**. [New archives](direct/continuation/) · [35-trillion plan](COVERAGE.md#direct-plan-for-the-35-trillion-bridge)

## What the public files establish

Every command in this README reads only files in this directory; none needs network access or an account.

- `sha256sum -c evidence.sha256` reads the 65 regular files under this directory other than the Markdown files and the manifest itself, and compares them with digests recorded on 24 November 2026. It establishes only that the files are the released ones. On 25 November 2026 the Blaxel workspace name was removed from `cloud/baseten_prime_pilot/launch_sandbox.py`, which now reads it from `BL_WORKSPACE`, and that file's digest was updated.
- `bash replay.sh` decodes and verifies all **15,018,635** power rows in `direct/sealed` and `direct/continuation`, the four million-row square archives in `squares`, both Oppermann files (1,100,000 bases, two primes each), the two cloud smoke samples and the four Pratt certificates in `direct/examples`. It then recomputes the square-to-power nesting credits and the retained-coverage ledger (verifying the 105 alternative witnesses it uses) and prints the remaining workloads. It stops at the first failure.
- With Sorenson and Webster's verification through $m=70{,}500{,}000{,}000{,}000$ and the paper's treatment of small bases, these certificates prove the $11/5$ statement for every $n\le3{,}883{,}865{,}444{,}451$ and the square statement for every $m\le70{,}500{,}002{,}100{,}000$. They also cover isolated ranges: the other power rows in the [coverage ledger](COVERAGE.md#direct-power-witnesses); the power bases $4{,}616{,}019{,}348{,}273$–$4{,}616{,}019{,}397{,}498$ and $5{,}336{,}699{,}182{,}690$–$5{,}336{,}699{,}231{,}206$, through the square pilots; the square pilot ranges; and 11,894,934 further square bases.
- For every other base, $3{,}883{,}865{,}444{,}451<n<3.5\times10^{13}$ and $70{,}500{,}002{,}100{,}000<m\le10^{14}$, the finite results rest on the verification done inside the 2026 run and on its audit. The run's schedule digest, pilot-manifest digests and audited totals are public in [combined-production-results.json](cloud/baseten_prime_pilot/combined-production-results.json); its archive is not. A referee with read access has replayed 160,000,000 of its pilot rows. A full replay of the pilot is open. [Status of the run's evidence](cloud/baseten_prime_pilot/README.md#status-of-the-evidence)

So the two finite results have been verified independently only on the ranges in the third item and on those 160,000,000 bases, not in full.

## Further checks

For a quick independent test of one complete tract with the Python standard library alone, run

```bash
python3 -S direct/power_pilot_certificates.py \
  13672702248661 13672702248861 \
  direct/sealed/13672702248661-13672702248861.iw.gz
```

The output should read `Verified all 201 witnesses for 13672702248661 through 13672702248861.` This establishes the 201 bases in that archive.

The original direct kit's manifest, `direct/SHA256SUMS`, is kept unchanged as a historical record; `direct/RUN.txt`, which it covers, still refers to it. Three of its 17 files (`check_power_witnesses.cpp`, `power_pratt_fallback.py` and `verify_11_5.cpp`) were later extended for the 2026 run, with exclusion lists and square modes, so `(cd direct && sha256sum -c SHA256SUMS)` reports those three as changed. Their current versions are covered by `evidence.sha256`. To check the other 14 entries, run

```bash
(cd direct && grep -v -e ' check_power_witnesses\.cpp$' -e ' power_pratt_fallback\.py$' -e ' verify_11_5\.cpp$' SHA256SUMS | sha256sum -c)
```

Square pilots have hashes of both the compressed and decoded streams. [Square archives, proofs and commands](squares/README.md) · [Machine-readable square results](squares/results.json)

The two regeneration commands below show that the released generators reproduce archived witness streams byte for byte; they establish nothing beyond what `replay.sh` checks. To regenerate the ten-million-base continuation, build the three portable binaries in `direct/bin` as described in the runbook and execute the following from this directory. Keep the exact shard bounds because the generator's internal search windows depend on the partition. The command independently verifies every prime after reopening the new archive. [Build instructions](direct/RUN.txt)

```bash
output=$(mktemp -d)
INTERVAL_GENERATOR="$PWD/direct/bin/portable_power_witness" \
  bash direct/certify_power_shard.sh 3883855444452 3883865444451 "$output" direct/bin
set -o pipefail
gzip -dc "$output/3883855444452-3883865444451.iw.gz" | direct/bin/interval_witness_codec unpack | sha256sum
```

The decoded decimal witness stream has SHA-256 `83982bea589b46f5d34286d5a83ac68bae70b63d537a4d0a7c59f5f7a190e15b`.

The 35-trillion pilot uses the original GMP generator with the same codec and independent verifier. With the binaries above built, regenerate the final million bases below the cutoff using these commands. [GMP generator](direct/verify_11_5.cpp)

```bash
c++ -O3 -std=c++17 direct/verify_11_5.cpp -lgmpxx -lgmp -o direct/bin/verify_11_5
output=$(mktemp -d)
INTERVAL_GENERATOR="$PWD/direct/bin/verify_11_5" \
  bash direct/certify_power_shard.sh 34999999000000 34999999999999 "$output" direct/bin
set -o pipefail
gzip -dc "$output/34999999000000-34999999999999.iw.gz" | direct/bin/interval_witness_codec unpack | sha256sum
```

The decoded GMP pilot stream has SHA-256 `443be3712cd1987b4d0a8e05b4af6b9126cfd45094a2ebe0ae41476a112379b3`.

## What each saved row proves

The direct verifier checks exact powers at both strict endpoints. In the fast certificate let $F$ be a power of two dividing $p-1$ with $F^3>p$. The verifier checks $3^{(p-1)/2}\equiv -1\pmod p$. For a prime divisor $q$ of $p$, the multiplicative order of 3 modulo $q$ divides $p-1$ and fails to divide $(p-1)/2$. Therefore $F$ divides $q-1$. A composite candidate must have exactly two prime factors counted with multiplicity, each of the form $1+aF$. If $p=(1+aF)(1+bF)$ and $a+b\ge F$, then $ab\ge a+b-1$ implies $p\ge 1+F^3$. Hence $a+b<F$. The quotient and remainder on dividing $(p-1)/F$ by $F$ would be $ab$ and $a+b$. A negative or nonsquare discriminant rules this out. The verifier can also accept immediately when $(F+1)^2>p$ after the order test. The compressed offsets and CRC protect framing. The arithmetic checks establish primality and interval membership. Certificate derivation · [Standard-library verifier](direct/power_pilot_certificates.py) · [Independent C++ verifier](direct/check_power_witnesses.cpp)

## Resume the computation

- [The original direct runbook](direct/RUN.txt) gives GMP and compiler setup, portable and IFMA builds, local timing, and production shard commands. Its job planner divides the historical contiguous residual into 28,771 jobs of at most a billion bases and deliberately includes some cells now known to be covered. All endpoints in the runbook and the updated ledger are inclusive. [Updated coverage](COVERAGE.md)
- The shard runner generates primes, packs the rows, reopens and replays the archive, and publishes it under a canonical name. A failed search in the chosen arithmetic progression leaves that base undecided. The original GMP searcher explores more candidates. The fallback generator uses SymPy to propose a prime and build a recursive Pratt proof, which the Python standard library can then verify independently. The joined range checker accepts both compressed runs and singleton proofs and rejects missing or overlapping bases. [Shard runner](direct/certify_power_shard.sh) · [Range checker](direct/power_sweep_plan.py) · [Fallback](direct/power_pratt_fallback.py)
- The historical 78-crossing estimate gives an upper bound on the number of possible failures under the project's analytic assumptions. It supplies no 78 indices to check. The 78 timed controls in the feasibility note were selected from already covered positions. Feasibility and localization discussion
- [Cloud measurements and forecasts](cloud/README.md) distinguish the completed Baseten trial, the local Google worker tests and the estimates for Google H3, Mac, clusters and GPUs. Search and codec development preserves alternate implementations and diagnostics. [Source provenance](PROVENANCE.md)
