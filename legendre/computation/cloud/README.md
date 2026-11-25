# Compute trials and projected fleet sizes

The November 2026 Baseten sandbox fleet completed the combined verification in 18 hours 53 minutes. See the [production run record](baseten_prime_pilot/README.md#completed-production-run) for measured rates, archive size, and the coverage audit. The figures below describe earlier Training Job and local calibration work.

## Measured CPU work

An Intel Xeon Platinum 8573C core with AVX-512 IFMA generated, wrote, reopened and independently verified one million power witnesses in 3.50 and 3.68 CPU seconds at the two ends. Compressed files used 867–881 KB per million. Scaling those figures gives about **28,000–29,400 core-hours and 25 TB** for $11/5$. Measured square pilots near 70.5, 85.25 and 100 trillion used 3.80, 3.84 and 3.91 CPU seconds per million. Together these imply **57,700–59,900 core-hours and 49 TB** for the combined plan. At 80% scaling, 1,024 similar cores project to 34–36 hours direct or 70–73 hours combined. A portable single Linux core achieved 174,629 direct bases/s. Eight such cores at ideal scaling would take about eight months, or sixteen about four months. Apple hardware requires a local calibration. [Raw measurements](../direct/measurements/) · Core-count table and assumptions

The Baseten pilot requested 8 vCPUs and 16 GiB RAM, received an `8x32` placement after 34 seconds and ran the scalar backend. The median verified direct throughputs at 1, 4 and 8 workers were 153,714, 636,080 and 1,001,393 bases/s. Corresponding square throughputs were 162,167, 669,347 and 1,101,438/s. The timed workload performed 156 million sample rows, including repeated ranges across endpoints, workloads and repetitions. Trial archives were discarded after each measurement. The downloaded, independently replayed million-row direct sample survives in [the ledger](../COVERAGE.md). End-to-end timing includes local storage, decompression and independent arithmetic replay. The optional shared-store throughput test was not completed. A 32-vCPU/64-GiB placement stayed queued for 30 minutes and was stopped. A 64-vCPU/128-GiB request was rejected. Trial results · [Configuration, test and storage probe](baseten_prime_pilot/README.md)

## Session forecasts

| Service and goal | 24-hour fleet | 48-hour fleet | Projected compute |
|---|---:|---:|---:|
| Baseten, direct | 480 nodes | 240 nodes | $4,140 |
| Baseten, combined | 900 nodes | 450 nodes | $7,780 |
| Google H3, direct | 20 VMs | 10 VMs | $1,960–2,055 |
| Google H3, combined | 41 VMs | 21 VMs | $4,035–4,190 |

Baseten uses the measured eight-worker rates, the historical $0.00691/node-minute rate and 80% fleet efficiency. The forecasts round up for a three-hour reserve on day one or six hours over two days. The corresponding 48-hour shared-storage targets are about 170 MB/s direct or 330 MB/s combined. The H3 forecast assumes each of the 88 physical cores on an Iowa `h3-standard-88` matches our local fast Xeon. The quoted rate was $4.9236 per VM-hour. A Spot scenario gave roughly $940–990 or $1,940–2,015 before interruptions. Estimated Iowa storage was $470/$920 per month for the two archive sizes. Only the Baseten rows have a measured per-node speed. Simultaneous fleet placement and these deadlines are unverified. Sizer · [Google H3 specifications](https://docs.cloud.google.com/compute/docs/compute-optimized-machines) · [CPU pricing](https://cloud.google.com/products/compute/pricing/compute-optimized) · [Spot rates](https://cloud.google.com/spot-vms/pricing) · [Storage pricing](https://cloud.google.com/storage/pricing)

The Google launcher, boot payload, serial decoder and Python-only replay are ready for a one-node calibration in a billing-enabled, authorized project. The tests archived here used a **local** Linux host. One test exported and reverified a 2,048-row serial sample. A separate four-row test exercised the larger worker matrix. Both ranges are duplicates of an existing direct certificate tract. The recorded chip, cgroup, rates and test dates identify the local environment. The source has no stored cloud credentials, authorization receipt for a Google VM, or live fleet result. Google worker instructions · [Local smoke reports and samples](gce_local_smoke/)

## GPU feasibility

The complete endpoint profiles measured IFMA search at 1.19–1.39 CPU seconds/million, independent GMP verification at 2.05–2.31, and archive stages plus SHA-256 at 0.32–0.37. Removing the entire search stage on the same fixed host at zero transfer cost gives an ideal end-to-end speedup of 1.50–1.52. Accelerating both search and independent verification could change that bound. A single-L4 Google machine priced at $0.854/hour would need approximately 4.2–4.4 million fully archived and verified direct cases/s to beat the H3 forecast. There is no measured GPU implementation. CPU profile · Profile driver · [Google GPU pricing](https://cloud.google.com/products/compute/pricing/accelerator-optimized)
