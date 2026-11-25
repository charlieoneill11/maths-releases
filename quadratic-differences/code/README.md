# Four-colour quadratic differences

Write $E=|e|$, $F=|f|$ and $P(x)=ex^2+fx$. Two distinct integers are adjacent when their absolute difference is $|P(d)|$ for some integer $d$. The first interval that admits no proper four-colouring has length $W(P;4)$.

**The optimal constant is $C_4=57$.** For every coefficient pair we prove the stronger bound $W(P;4)\le57E+39F+1$. The pure square attains 57, and $x^2+x$ attains 39 when the quadratic coefficient in the bound is fixed at 57. A periodic colouring settles the requested $58\times58$ grid. A different argument uses a $12\times58$ rectangle, propagation of three alternative colours, and the primitive kernel of the scalar projection. The decisive SAT refutation is saved and independently replayable. [Complete proof and replay](forcing.md)

## Exact thresholds

| $j$ in $x^2+jx$ | $W$ | Edges at $W$ | Provenance |
|---:|---:|---:|---|
| 0 | 58 | 266 | Canakci et al., independently replayed |
| 1 | 97 | 543 | Kumthekar et al., independently replayed |
| 2 | 82 | 461 | Rebuilt from the definition after the requesting chat supplied the candidate |
| 3 | 81 | 422 | Rebuilt from the definition after the requesting chat supplied the candidate |
| 4 | 75 | 418 | Computed here |
| 5 | 89 | 428 | Computed here |
| 6 | 73 | 418 | Computed here |
| 7 | 49 | 215 | Kumthekar et al., independently replayed |
| 8 | 53 | 264 | Computed here |

The following words give the colours of $1,2,\ldots$ in order. For $j=2$ the permitted positive distances below 82 are $1,3,8,15,24,35,48,63,80$. For $j=3$ those below 81 are $2,4,10,18,28,40,54,70$.

~~~text
j=2, N=81
010121232020131202313020202313020202313030202313131202313131202323030101313020131
j=3, N=80
02112033021120330211203302203302112033021120330211203311203302112033021120330211
~~~

Each lower certificate colours $W-1$ vertices. Each upper certificate refutes the four-colouring CNF at $W$. Restricting a colouring to a shorter interval proves that these two checks give the exact threshold. The encoder enumerates both signs of $d$. The verifier independently tests whether one of $j^2\pm4k$ is a nonnegative square with square root congruent to $j$ modulo two. It checks every pair, compares the entire edge set to the encoder, and calls a separate DRAT checker. The four Boolean variables at a vertex specify exactly one colour. Each edge forbids each of its four monochromatic assignments. Two unit clauses name the distinct colours at the ends of the first edge. [All colouring words](thresholds.json) · [Refutations](certificates/) · [Verifier](verify.py)

### Structure of the small family

Completing the square gives the positive distances $|s^2-k^2|$ for $j=2k$. For $j=2k+1$ they are $2|T_s-T_k|$, where $T_s=s(s+1)/2$. In both formulas $s$ ranges over all integers and zero distances are discarded. In the odd case the parity classes separate. Dividing each by two reduces the critical instance to one interval with shifted triangular distances, of lengths 49, 41, 45 and 25 for $j=1,3,5,7$.

A common packing proof works for $j=1,3,7$. The reduced graphs respectively have no independent set of size 13, 11 or 7, although one colour class must have at least that size. To check this, translate the least chosen point to zero. With $k$ points still needed, try each next point in increasing order, deleting it, its predecessors and all remaining points at a forbidden distance from it. Fewer than $k$ candidates closes the branch. The independent recursion in the verifier uses just the integer distance test. For $j=5$ the reduced graph actually contains the independent 12-set $\{0,1,5,9,10,14,15,20,31,36,37,41\}$ on $[0,44]$, so the four-class covering condition matters there. [Packing check](verify.py)

## The square and a smaller rectangle obstruction

For the square, take the colour at $(u,v)$ from row $u\bmod 8$, column $v\bmod16$ of the saved tile, with indices starting at zero. Checking the 128 residues against both $(d,d^2)$ and $(d,-d^2)$ for $1\le d\le7$ proves properness on all of $\mathbb Z^2$. The verifier also checks all 29,176 edges of the requested square individually. The tile was found by identifying periodic coordinates in the SAT model and extracting a satisfying assignment. [Periodic colouring](grid-tile.txt)

A second periodic colouring permits a local change. On the even-sum component use row $u\bmod8$, column $\lfloor(v\bmod32)/2\rfloor$ of the second tile. Copy this to the other component by translating one horizontal unit. All 28 neighbours of the origin have colour 2. The origin may therefore take any of 0, 1 and 3. For any two extra edges with a common endpoint, translate that endpoint to the origin and pick an available colour different from both other endpoints. This also handles one arbitrary extra edge. Thus a planar obstruction using the seven step sizes needs at least two disjoint added edges, or three or more added edges. [Flexible tile](flexible-tile.txt) · [Full-period and neighbourhood check](verify.py)

For the authors' rectangle $Q=[0,10]\times[0,64]$, integer endpoints inclusive, the encoder reproduces 715 vertices and 4,864 edges. Each allowed step preserves the parity of $u+v$. The even component has 358 vertices and 2,436 edges and is already non-four-colourable. We also certified the following proper subset $S$ of that component.

* Retain every even-sum point in rows $1$ through $63$.
* In row zero retain $u=8,10$. In row 64 retain $u=0,2$.

The induced graph on $S$ has 350 vertices and 2,362 edges. The two surviving step-eight edges join $(8,0)$ to $(0,64)$ and $(10,0)$ to $(2,64)$. The CNF of $S$ has 1,400 variables and 11,900 clauses. Kissat refuted this CNF and drat-trim checked the proof. The same independently checked procedure reproduces the published rectangle. [Encoder](encode.py) · [Replay script](replay_grids.sh)

### Projection and exceptional coefficients

Negating the polynomial or its argument preserves absolute distances. We may use $P(d)=Ed^2+Fd$. For a fixed integer colouring, pull back the colour at $1+Fu+Ev-\min_S(Fu+Ev)$. On an edge the signed label difference is $Fd+Ed^2$ or $Fd-Ed^2$, with absolute value $|P(d)|$ or $|P(-d)|$. Equality of labels at nonadjacent points is harmless. With $E,F>0$ an edge can collapse only for $F=dE$, $1\le d\le8$.

The minimum over $S$ is $m=\min(8F,E+F,2E)$, attained among $(8,0),(1,1),(0,2)$. Reflection $(u,v)\mapsto(10-u,64-v)$ preserves $S$, so the maximum is $64E+10F-m$. In every noncolliding case this gives

$$ W(P;4)-1\le64E+10F-2\min(8F,E+F,2E). $$

For $E\ge7F$ this is $64E-6F$, at most $57(E+F)$ for $E\le9F$. For $F\le E\le7F$ it is $62E+8F$, and for $0<E\le F$ it is $60E+10F$. Both satisfy the same sharp target throughout their stated ranges. The authors' generic rectangle alone reaches the target for $7E\le47F$.

The pair of coefficients $(64,-6)$ is best possible near the pure-square axis among projections of **any fixed finite lattice obstruction** with steps $(d,\pm d^2)$. To see this, let $h$ be its vertical span. If $h<64$ only the seven tile-colourable step sizes occur. If $h=64$, write $a$ for the smallest horizontal coordinate on the bottom row and $b$ for the largest on the top row. A size-eight step must join those two rows. If $b-a\le-7$, it must start at the bottom at $x=a$ or $a+1$ and end at $x-8$ on top. The two possible edges lie in different parity components. Each component then has at most one extra edge and the flexible tile colours it, a contradiction. Thus $b-a\ge-6$. For a fixed finite set, sufficiently small positive $F/E$ makes the bottom and top rows attain the label extrema, giving span $hE+(b-a)F$. The cropped obstruction attains $64E-6F$. Any further improvement in these asymptotic coefficients must involve an argument beyond projecting a fixed finite lattice obstruction.

For $F=jE$, $1\le j\le8$, Proposition 2.1 of Kumthekar et al. gives $W(P;4)=E(W(x^2+jx;4)-1)+1$. Indeed a distance multiplied by $E$ stays in one residue class, where division by $E$ restores the unscaled graph. At the lower endpoint one can colour each residue class separately, and at the upper endpoint one class is long enough to force the pair. Every table entry has $W-1\le96\le57(1+j)$. For $E=0$, each class modulo $F$ is a clique and $W(Fx;4)=4F+1$. For $F=0$, the pure-square value gives $W(Ex^2;4)=57E+1$, attaining the lower bound on $C_4$. The input excludes $E=F=0$. [Proposition 2.1 and Section 4](https://arxiv.org/html/2611.14913v1)

## How the near-axis range is settled

For $E\ge6F>0$, every scalar colouring on $[0,57E+11F]$ would pull back to a proper colouring of the even-sum component of a $12\times58$ rectangle. Certain assignments on eight or ten vertices force a repeating four-colour pattern across a subinterval. A primitive translation preserves its integer label and changes its required colour. The independently checked rectangle refutation shows that every proper colouring contains one of these assignments. Together with the cropped bound and the exceptional cases, this proves $C_4=57$. [Winding proof, clause audit and binary certificate](forcing.md)

The strip formulation gives a further quantitative result. The limiting worst ratio as $F/E$ tends to zero through positive values is an integer in $[52,57]$. A cycle of five row words proves the lower estimate. Additional computational checks include direct scalar refutations on the six rays $E/F=10,\ldots,15$ and 1,605 refutations for short-period binary partitions of the colours. [Strip results](strip.md) · [Binary period calculation](palette.md)

There is a limitation on any proof by small graphs in the hardest range. If $65F<7E$, then $64E-8F>57(E+F)$. All distances from $|d|\ge8$ exceed the available span at the target, since $Ek^2-Fk$ is increasing for $k\ge8$. Thus every scalar edge there comes from a step of the colourable infinite lattice. A proof in this range must use identifications under projection.

More quantitatively, write $p=E/\gcd(E,F)$, $q=F/\gcd(E,F)$. Any non-four-colourable scalar subgraph in this range contains a simple cycle of length at least $\lceil p/7\rceil$, or $\lceil2p/7\rceil$ when $p+q$ is odd. To see this, choose one signed lattice step for each oriented edge and its negative for the reverse edge. If the steps sum to zero on all simple cycles of a component, integrate them along a spanning tree. This gives a map to the lattice that takes every edge to an allowed step, so the periodic tile colours the component. Otherwise a simple cycle sums to a nonzero kernel vector $k(p,-q)$. Its first coordinate has absolute value at most seven times the cycle length. Each step has even coordinate sum, forcing $k$ even when $p+q$ is odd. In particular no fixed vertex budget can settle arbitrarily large primitive $p$ in this range.

The proof also excludes cyclic witnesses of every modulus. Indeed, suppose a word on $\mathbb Z/M\mathbb Z$ separates all shifts $ad^2+bd$ for $1\le|d|\le7$. Fix $F>0$ congruent to $b$ and let $E$ tend to infinity through $a\bmod M$. The word colours $[64E-8F]$ because the first omitted positive distance is at least $64E-8F$. Hence $W-1\ge64E-8F$. Dividing by $E+F$ would give $C_4\ge64$, contradicting the theorem.

We exhaustively ruled out these cyclic words through modulus 192. The search reduces a common divisor of $(a,b,M)$ by restricting to a residue class, multiplies both residues by a unit to relabel vertices, and allows $b\mapsto-b$ because the argument takes both signs. In the reduced cases 2,507 had a loop and 12,129 required an exhaustive four-colouring check. This independent search preceded the proof for arbitrary moduli. [Reproducible cyclic search](cyclic_search.py)

## Reproduction and provenance

Run from this folder. The short replay uses Python's standard library, a C compiler and the copy of drat-trim in this folder.

~~~sh
cc -O2 drat-trim.c -o /tmp/q4-drat-trim
PYTHONDONTWRITEBYTECODE=1 python3 verify.py /tmp/q4-drat-trim
sh replay_forcing.sh /tmp/q4-drat-trim
python3 cyclic_search.py 192
~~~

For the larger rectangles, build the pinned upstream solver in a fresh temporary directory. The script generates one binary DRAT proof at a time and checks it before removing the temporary files. Allow several minutes on one CPU and temporary storage for a proof of about 90 MB.

~~~sh
builddir=$(mktemp -d)
git clone --quiet --depth 1 --branch rel-4.0.4 https://github.com/arminbiere/kissat.git "$builddir/kissat"
test "$(git -C "$builddir/kissat" rev-parse HEAD)" = 8af8e56f174b778aef3aa45af9f739b2a5f492c2
(cd "$builddir/kissat" && ./configure --quiet && make -s -j2)
sh replay_grids.sh "$builddir/kissat/build/kissat" /tmp/q4-drat-trim
~~~

| Checked graph | SHA-256 of DIMACS input | SHA-256 of binary proof in this run |
|---|---|---|
| Published rectangle, even component | 28b969e5f4669bfc7a5a3ac5cab132d347afda1fe96cc456dce92307bccf9a83 | 65e0256723de8b27c8a6c60d58ac7e7cc4b998822d977eb3c51028e5e82c8c6d |
| Cropped rectangle | 4d7a888d0c668c6f11e44ad3af3bf912e3d67ea095d2e148d33707c7bc1e4a10 | 9e68dd7e4bf48374949584d63102c51d7dea3e80f11e19c3c70776223b5c6c1d |

The checker source had SHA-256 d834b649f437e091597f5347f259b9f681087f89ca0844d0cee250a1a1a0c2ee. It reported VERIFIED for both rectangles, using 46,410,711 and 44,764,107 resolution steps respectively. For the interval proofs the generator used Glucose via python-sat 1.9.dev25 on CPython 3.12. To regenerate the saved files in a checkout, run the following optional commands.

~~~sh
venvdir=$(mktemp -d)
python3 -m venv "$venvdir"
"$venvdir/bin/python" -m pip install 'python-sat==1.9.dev25'
PYTHONDONTWRITEBYTECODE=1 "$venvdir/bin/python" generate.py
PYTHONDONTWRITEBYTECODE=1 python3 verify.py /tmp/q4-drat-trim
~~~

This investigation began from maths main commit 444616794623787c61dc91ad85ad7c16aeb23a51. The first four SAT checks used the supplied candidate endpoints for $j=2,3$. For the remaining $j$ a monochromatic-pair threshold of at most 97 from the paper bounded a binary search, followed by fresh proof runs at both endpoints. The grid tests began with a 10,000-conflict pilot and then used a single solver per instance. All evidence here comes from direct computation or the cited mathematics. No additional model or inference endpoint was called.

The public-work check on 25 November 2026 covered the preprint's Sections 1, 4 and 6, its exact-value table, the earlier pure-square paper, and web searches by preprint identifier, authors, polynomial, proposed thresholds and the optimal-constant question. These searches found the published $j=1,7$ entries and the pure square, and located no overlapping exact report for the other six entries or determination of the optimum. This is a dated search result. [Kumthekar, Gasarch, Regli and Whitehouse](https://arxiv.org/html/2611.14913v1) · [Canakci, Christenson, Fleischman, Gasarch, McNabb and Smolyak](https://arxiv.org/abs/2312.01159)
