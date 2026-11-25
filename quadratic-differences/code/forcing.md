# The optimal constant is 57

For integers $e,f$ not both zero, put $E=|e|$ and $F=|f|$. Then
$$W(ex^2+fx;4)\le57E+39F+1.$$
In particular $C_4=57$. The pure square attains the coefficient 57. With that coefficient fixed, $x^2+x$ attains the coefficient 39 since its threshold is 97.

The new part is the estimate $W(px^2+qx;4)-1\le57p+11q$ for $p\ge6q>0$. We prove it below for all such integers, including noncoprime pairs. The finite computation uses 348 vertices and has a saved, independently checkable refutation.

## Pullback to the lattice

Translate the scalar interval to start at zero. Suppose it has a proper colouring on $[0,57p+11q]$. At a lattice point $(u,v)$ use the colour of $qu+pv$ whenever this label is in the interval. A displacement $(d,\pm d^2)$ has absolute label difference $|pd^2\pm qd|$. These differences are nonzero for $1\le d\le7$. Thus the even-sum points in $[0,11]\times[0,57]$ give a proper colouring of the ordinary rectangle graph with these steps.

There is an additional restriction on any colouring obtained from integer labels. Choose $0\le u_0\le7$, $2\le v_0\le19$, with $u_0+v_0$ even. Use physical points $(u_0+2x,v_0+4y)$ with the parity of $x+y$ fixed. Differences $(\pm d,\pm d^2)$ in $(x,y)$ are valid physical edges with parameter $2d$ for $d=1,2,3$.

Let $L=\{(a,b)\in\mathbb Z^2:a+b\equiv0\pmod2\}$. On either coset the four classes modulo $2L$ are distinguished by
$$\phi(x,y)=\bigl(x\bmod2,\ \lfloor(y-x)/2\rfloor\bmod2\bigr).$$
Take any bijective assignment of four colours to these four classes. Call its value at a point the prescribed colour. Along any translation in $L$, the change of the second bit is $(b-a)/2\bmod2$, including on the odd coset.

## Why agreement in three columns is impossible

Set $z=qu_0+pv_0$ and restrict attention to the physical points whose scalar labels belong to
$$I=[z-2p,\ z+38p+4q].$$
The endpoints are $qu_0+p(v_0-2)$ and $q(u_0+4)+p(v_0+38)$. They lie in the original interval. The span of $I$ is $40p+4q$.

For a site in column $x$, look at predecessors $(x-d,y\pm d^2)$. Each alternative to the prescribed colour has two possible predecessors with that colour, one above and one below. The entries are changes of the two bits, with addition modulo two.

| Change of bits | $d$ for the lower predecessor | $d$ for the upper predecessor | Sum of the absolute label changes |
|---|---:|---:|---:|
| $(1,0)$ | 1 | 3 | $40p-4q$ |
| $(1,1)$ | 3 | 1 | $40p+4q$ |
| $(0,1)$ | 2 | 2 | $32p$ |

Indeed the lower predecessor changes the scalar label by $-2dq-4pd^2$ and the upper by $-2dq+4pd^2$. If a site has label in $I$, at least one member of each pair also has label in $I$. Otherwise the sum in the last column would exceed the span. Once the prescribed colours hold on all sites of $I$ in three consecutive columns, properness forces them on the next column, hence on every subsequent column.

The scalar colouring cannot have this property. In the basis $(1,1),(0,2)$ of $L$, the linear part of the label has coefficients $A=2q+4p$ and $B=8p$. Its kernel contains the translation with basis coordinates $(B/g,-A/g)$, where $g=\gcd(A,B)$. Its $x$ coordinate is positive and its two basis coordinates are coprime. It is therefore outside $2L$. Translating a site by this vector preserves its scalar label and keeps it in $I$, while changing its prescribed colour. Taking a site in the initial three columns and moving forward gives a contradiction.

In columns $x=0,1,2$, the sites of $I$ are exactly those with $0\le y\le9$ and the chosen parity. To see this, subtract $z$ from the label to get $2qx+4py$. Rows $-1$ and $10$ fall outside the interval since $p\ge6q$. Moreover every auxiliary site with $-6\le x\le8$ and $0\le y\le9$ has label in $I$, since $-12q\ge-2p$ and $36p+16q\le38p+4q$. These bounds permit local deductions even when an auxiliary site is outside the displayed rectangle.

## The finite calculation

On $0\le x\le8$, $0\le y\le9$ in each parity, start with a subset of the fifteen sites in the first three columns and assign their prescribed colours. Whenever neighbours already carry the other three colours, fill the forced site. Enumerating the subsets gives four inclusion-minimal sets of size eight and four of size ten for each parity. Reflecting in $x=1$ or $y=9/2$ preserves the four-class partition up to renaming and stays within the auxiliary bounds above. After deduplication there are eight patterns of each size. Each pattern forces the entire fifteen-site block, so every permutation of its colours is forbidden in the pullback.

For example, one eight-site assignment in the even coset gives four different colours to the following four groups, in coarse coordinates.

| Colour | Sites |
|---|---|
| 0 | $(0,0)$ |
| 1 | $(0,2),(0,6),(2,0)$ |
| 2 | $(1,5),(1,9)$ |
| 3 | $(1,3),(1,7)$ |

The DIMACS input uses four variables per even-sum vertex of the ordinary, horizontally unwrapped $12\times58$ rectangle. The grid contributes 2,352 edges. The formula requires exactly one colour per vertex, forbids monochromatic edges, and names the distinct colours at the ends of one edge. For each of the 72 choices of $(u_0,v_0)$ there are 16 forbidden patterns and 24 colour permutations. The complete input has 1,392 variables and 39,494 clauses.

Kissat 4.0.4 refuted this formula. The independent drat-trim check of its original binary proof used 35,621,617 resolution steps. A separate standard-library audit decodes the actual DIMACS clauses. It rebuilds the grid by testing every pair of vertices, checks the two colour names, and justifies all 27,648 pattern clauses. For each forbidden assignment it propagates literal colours in the auxiliary box and tests equality of the resulting colours against membership of pairwise differences in $2L$. The audit operates independently of the pattern generator. This proves that the supposed scalar colouring cannot exist. [Encoder](forcing.py) · [Clause audit](audit_forcing.py) · [Saved proof](certificates/near-axis.drat.xz)

## The remaining coefficients and sharpness

Sign symmetry permits $e=E$ and $f=F$. For $E\ge6F>0$ the estimate just proved gives $W-1\le57E+11F$. For $0<E<6F$ outside collisions, the cropped rectangle gives $60E+10F$ when $E\le F$ and $62E+8F$ when $F\le E<6F$. These are at most $57E+13F$ and $57E+38F$, respectively. For $F=jE$, $1\le j\le8$, scaling and the eight exact thresholds give $W-1=E(W(x^2+jx;4)-1)\le57E+39F$, with equality for $j=1$. For $E=0$ we have $W=4F+1$. For $F=0$ we have $W=57E+1$. This proves the asserted bound and determines the optimum. [Rectangle proof, scaling and exact thresholds](README.md)

## Replay

Run from the problem folder. The saved-certificate route uses Python's standard library, a C compiler, xz, and the repository's checker. It needs temporary disk space for the decompressed proof. The build and verification commands for the cropped rectangle and the nine interval certificates appear in the main reproduction instructions. [Other certificates and provenance](README.md#reproduction-and-provenance)

~~~sh
cc -O2 drat-trim.c -o /tmp/q4-drat-trim
sh replay_forcing.sh /tmp/q4-drat-trim
~~~

The checked run and the stored certificate have the following SHA-256 digests. The stored proof is the binary output of drat-trim with `-C -l`, compressed with `xz -6 -T1`.

| Artifact | SHA-256 |
|---|---|
| DIMACS input | 0e39e712bfba5a99cb880ded1c66fcfbc175b60b199e48bc432241d31fe28832 |
| Original Kissat proof | d5eb1fe0e1bd2aaebba8373216e6b942ef30d2331aa8f9b36ff0a431a4fa4765 |
| Trimmed binary proof | 1b8b8f21348fd5c06d508b157a49feb5881daf203c6ba1c08391e9c3a1ab6829 |
| Stored xz file | 41e5c90b89a72038ab9d551a98752e369b01b6985679e7f1e8934d0738ada6f3 |

To regenerate an independent proof with the pinned Kissat build from the main instructions, run the following in a shell with `set -e`.

~~~sh
outdir=$(mktemp -d)
python3 forcing.py cnf 12 58 > "$outdir/input.cnf"
python3 audit_forcing.py "$outdir/input.cnf"
status=0
"$builddir/kissat/build/kissat" "$outdir/input.cnf" "$outdir/fresh.drat" || status=$?
test "$status" -eq 20
/tmp/q4-drat-trim "$outdir/input.cnf" "$outdir/fresh.drat"
~~~

The pattern arose by inspecting the eight residue classes preserved by the even steps in the original periodic tile. Enumerating all 10,128 four-colourings of its 64-vertex parity torus up to colour permutation gave 4,608 with six affine components, 3,552 with seven, and 1,968 with eight. The separate command `python3 forcing.py audit` reproduces this observation. The proof uses the unwrapped rectangle. Its exhaustive refutation does not require a periodicity assumption on the unknown colouring.
