# Coverage ledger

## Completed combined verification

The November 2026 run certifies every square interval for $1\le m\le 10^{14}$ and every $11/5$ interval for $1\le n<35{,}000{,}000{,}000{,}000$. These finite results use the published square prefix, retained certificates, newly verified witnesses and whole-square nesting. The run's new witnesses are in a private bucket. Only the retained certificates in this directory can be replayed publicly, with `replay.sh`; they cover every $n\le3{,}883{,}865{,}444{,}451$ and every $m\le70{,}500{,}002{,}100{,}000$, and the isolated ranges below. The remaining bases rest on the verification done inside the run and on its audit: a referee has replayed 160,000,000 of the 800,000,000 pilot checks, and no production check has been replayed outside the run. [What the public files establish](README.md#what-the-public-files-establish). The all-integer $11/5$ result also needs the paper's analytic argument, which uses the Riemann hypothesis, now proved by Alpöge.

| Workload | Pilot checks (verified in the run) | Audited production checks | Total new checks |
|---|---:|---:|---:|
| Square | 64,000,000 | 29,499,920,005,066 | 29,499,984,005,066 |
| Direct $11/5$, fast | 704,000,000 | 27,362,594,754,255 | 27,363,298,754,255 |
| Direct $11/5$, GMP | 32,000,000 | 2,299,966,999,999 | 2,299,998,999,999 |
| Combined | 800,000,000 | 59,162,481,759,320 | 59,163,281,759,320 |

The final audit reconciled all 319,488 production shards with the frozen schedule. The calculations below record the pre-production ledger. [Run record and replay instructions](cloud/baseten_prime_pilot/README.md#completed-production-run) · 35-trillion upper-tail argument

All ranges below include both endpoints. The outer mathematical reduction and the individual certificates have different dependencies. The sharper analytic cutoff in the appendix of the paper covers $n\ge 32,654,578,787,390$ if the table of maximal prime gaps up to $1.32\times10^{20}$ is complete, and $n\ge32,746,701,927,355$ without that table; the main theorem uses neither and needs only $n<35,000,000,000,000$ from the computation. The published square computation and interval nesting cover $n\le 3,883,853,444,450$. Those bounds leave 3,883,853,444,451 through 32,654,578,787,389 before project certificates are credited. Every direct, square, and Oppermann witness recorded below verifies by integer arithmetic alone. Bounds and published fallback

## Direct power witnesses

The imported archives are in [direct/sealed](direct/sealed/). The two new runs are in [direct/continuation](direct/continuation/). Each filename gives the inclusive bounds. The regression and codec fixtures were recovered on import, repacked, decoded byte-for-byte against the saved text, and verified independently. The low control sits within the published coverage.

| First $n$ | Last $n$ | Rows | Source |
|---:|---:|---:|---|
| 3,883,853,300,000 | 3,883,853,304,095 | 4,096 | Low control |
| 3,883,853,444,451 | 3,883,854,444,451 | 1,000,001 | Original direct pilot |
| 3,883,854,444,452 | 3,883,855,444,451 | 1,000,000 | Lower endpoint pilot |
| 3,883,855,444,452 | 3,883,865,444,451 | 10,000,000 | [Portable continuation](direct/continuation/3883855444452-3883865444451.iw.gz) |
| 10,000,000,000,000 | 10,000,000,008,191 | 8,192 | Arithmetic regression |
| 13,672,702,248,661 | 13,672,702,248,861 | 201 | Codec edge fixture |
| 32,650,000,000,000 | 32,650,000,002,048 | 2,049 | GMP/codec fixture |
| 32,654,400,000,000 | 32,654,400,004,095 | 4,096 | Upper control |
| 32,654,570,787,390 | 32,654,571,787,389 | 1,000,000 | Durable Baseten sample |
| 32,654,577,787,390 | 32,654,578,787,389 | 1,000,000 | Upper endpoint pilot |
| 34,999,999,000,000 | 34,999,999,999,999 | 1,000,000 | [35-trillion GMP pilot](direct/continuation/34999999000000-34999999999999.iw.gz) |

The binary archives now cover **15,018,635 distinct direct bases**, including the 4,018,635 imported rows. The three adjoining low-end runs extend continuous power coverage through **3,883,865,444,451**. The historical job planner uses the range $A=3,883,855,444,452$ through $B=32,654,577,787,389$, containing 28,770,722,342,938 bases. The low-end continuation covers its first ten million bases. The Baseten sample and the four in-band regression runs cover another 1,014,538. The four [Pratt demonstrations](direct/examples/) give explicit singleton proofs including $n=1$ and two previously archived direct bases. The remaining demonstration at $n=32,657,972,050,141$ lies above $B$.

## Composing square and power certificates

Sorenson and Webster verified the Oppermann half-intervals (with the usual small-base convention), and hence Legendre's assertion, through $m=70,500,000,000,000$. The archived paired witnesses extend both through $m=70,500,001,100,000$, with one prime in $(m^2,m(m+1))$ and another in $(m(m+1),(m+1)^2)$. The next million square-only rows continue Legendre through $m=70,500,002,100,000$. Three separate million-square pilots end at 85,250,000,000,000, 100,000,000,000,000 and 733,395,928,758,893. These remain isolated from the continuous prefix. [Published computation](https://doi.org/10.1007/s40993-024-00589-4) · [Square archive](squares/README.md)

In square-root coordinates each power interval has width $(n+1)^{11/10}-n^{11/10}>2$ in $[A,B]$, by convexity and $11^{10}A>20^{10}$. Each contains a full square interval with index $m=\lceil n^{11/10}\rceil$. The midpoint and target square pilots certify 97,742 distinct $n$ by whole-square nesting. The actual square witnesses prove **97,743**, including one boundary cell where the whole selected square interval need not fit.

To see this, let $p_m$ be the archived prime for square base $m$. The square roots of two successive witnesses are strictly increasing and less than two apart. They cannot skip over an entire power interval in square-root coordinates. For each pilot the first and last prime therefore certify every index between their exact power indices. A prime cannot be a power-interval boundary, since $p^5=n^{11}$ is impossible by unique factorization. Integer eleventh roots of the fifth powers of the endpoint witnesses give the two inclusive ranges.

| Square pilot | First $n$ | Last $n$ | Power cells |
|---|---:|---:|---:|
| Midpoint at 85.25 trillion | 4,616,019,348,273 | 4,616,019,397,498 | 49,226 |
| Target at 100 trillion | 5,336,699,182,690 | 5,336,699,231,206 | 48,517 |

The reverse direction takes $m=\lfloor\sqrt{p}\rfloor$ for each archived direct prime. The two lower imported direct archives prove 1,894,829 distinct $m$ inside the square-target band. The continuation adds 10,000,000 distinct square bases, from 70,500,039,934,593 to 70,500,239,607,437 with gaps. Together the three archives certify **11,894,829** square bases above the continuous prefix. Alternate archived choices of $p$ at some of the same $n$ prove **105 more** distinct $m$ outside those credits, the continuous prefix and the two high square pilots. Their complete triples and an arithmetic and disjointness check are included. [105 alternative witnesses](direct/alternative-square-credits.tsv) · Original nesting calculation · [Coverage replay](direct/check_retained_coverage.py)

## Bases left in the direct plan

The imported archives and the two square-implied runs left 28,770,721,230,657 bases in $[A,B]$. The continuation certifies the first ten million of these, leaving **28,770,711,230,657** bases in eight ranges.

| First $n$ | Last $n$ |
|---:|---:|
| 3,883,865,444,452 | 4,616,019,348,272 |
| 4,616,019,397,499 | 5,336,699,182,689 |
| 5,336,699,231,207 | 9,999,999,999,999 |
| 10,000,000,008,192 | 13,672,702,248,660 |
| 13,672,702,248,862 | 32,649,999,999,999 |
| 32,650,000,002,049 | 32,654,399,999,999 |
| 32,654,400,004,096 | 32,654,570,787,389 |
| 32,654,571,787,390 | 32,654,577,787,389 |

## Direct plan for the 35-trillion bridge

The paper's twelve-mode argument covers $n\ge 35,000,000,000,000$. Its finite computation includes the eight ranges above and two more. The GMP pilot covers the final million bases below this cutoff. The existing Pratt certificate at $n=32,657,972,050,141$ splits the rest of the added band into the two ranges below. This leaves **31,116,131,443,266** bases across ten ranges. The square indices of the 35-trillion pilot all exceed the combined plan's $10^{14}$ target. Classical bridge and its proof obligations · [Pratt certificate](direct/examples/pratt-fallback-32657972050141.json)

| First $n$ | Last $n$ |
|---:|---:|
| 32,654,578,787,390 | 32,657,972,050,140 |
| 32,657,972,050,142 | 34,999,998,999,999 |

## Combined plan through square base 100 trillion

A continuous square prefix through $10^{14}$ would supply witnesses for every remaining power interval through $n=5,336,699,231,206$. In the combined plan the charged square workload is $10^{14}-70,500,002,100,000-11,894,829-2,000,000-105=29,499,984,005,066$. Above the overlap ceiling the direct workload is $B-5,336,699,231,206-1,014,538=27,317,877,541,645$. Together **56,817,861,546,711** cells remain under this scheduling convention. The imported ledger reported 56,817,871,546,711 before the continuation. Additional deliberately shared witnesses could change the work count. A square-only route covering the entire historical reference band requires a contiguous 662,895,864,119,155 square cells, about 23 times the direct count.

Extending the combined plan to the 35-trillion splice leaves **29,663,297,754,254 direct power checks** above the overlap ceiling. This includes 27,363,298,754,255 bases supported by the fast generator and 2,299,998,999,999 assigned to GMP. The square workload stays **29,499,984,005,066**, for **59,163,281,759,320** checks before new pilot credits. The earlier combined total above uses the historical cutoff.

The completed 35-trillion plan covers the eight historical ranges and the added upper band. The square sweep establishes the finite extension through $10^{14}$. [Exact count and original scheduling geometry](direct/check_square_power_nesting.py)
