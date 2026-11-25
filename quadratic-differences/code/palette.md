# A short period in either colour bit is impossible

Suppose $p,q$ are coprime, $p>9q>0$, and $[0,57(p+q)]$ has a proper four-colouring for $pd^2+qd$. Set $g=\gcd(p+q,2p)$ and restrict to multiples of $g$, then divide their labels by $g$. In the resulting word on $[0,\lfloor57(p+q)/g\rfloor]$, **no partition of the four colours into two pairs gives a bit of period at most 64**. Here period $m$ only requires agreement at indices $m$ apart where both are in the word. The other bit may vary freely across the finite interval. A short period on the original interval would also restrict to a short period on this component.

This is a necessary condition on any counterexample. It tests a different class from a four-colouring that is periodic in both bits on the whole integer line.

## Lattice test

Take even-sum points in the $58\times58$ square, with coordinates $(u,t)$ where $t=(v-u)/2$. The normalized integer label is
$$au+bt,\qquad a=(p+q)/g,\quad b=2p/g.$$
Here $a,b$ are coprime. A binary word $B$ of period $m$ for the primary bit induces $B(au+bt\bmod m)$ on this lattice. Each allowed edge whose endpoints have the same primary bit must have opposite secondary bits. This applies to both signs of every step $1\le d\le7$ and to every subrectangle of the square.

It suffices to use the least period of the circular extension of the assumed primary word. A period word of length $m$ that repeats a shorter word has least circular period dividing $m$. To enforce minimality, for each prime $\ell\mid m$ require some $i$ with $B_i\ne B_{i+m/\ell}$. Multiplying $a,b$ by a unit modulo $m$ relabels the word. Reflecting the horizontal coordinate in either test rectangle replaces $a$ by $b-a$ and adds a constant phase. Both rectangle widths are odd, so the even-sum component is preserved. A phase shift and a global complement preserve the hypotheses.

## Primary bits depending only on the vertical coordinate

If $b=2a\bmod m$, the primary bit depends only on $v$. This case is impossible for every $m$.

Join rows $v,w$ of the same primary bit when $|v-w|=d^2$ for $1\le d\le7$. In either row of such an edge there are 29 positions of the correct parity in the square. The secondary word has period $d$ in that 29-letter sequence. Indeed the two lattice steps from $(u,v)$ via $(u+d,w)$ to $(u+2d,v)$ switch the secondary bit twice wherever both endpoints lie in the row.

Extend each nonisolated row to an infinite word using the period from any incident edge. This extension has each of the row's incident periods. To check this, let $e$ be the chosen period and $d$ another incident period. For the first $e$ positions, equality with the positions $d$ places later holds in the original word since $e+d\le14<29$. The $e$-periodic extension propagates those equalities everywhere. For adjacent rows the secondary bits at horizontal offset $d$ are opposite throughout the extensions. Both sides have period $2d$ in the original horizontal coordinate and the square contains a full period of comparisons.

Within each connected row component all the extended words are translates or complements of the root word. They therefore have common horizontal period $2h$, where $h$ is the gcd of the roots $d$ of all its edges. Choose an integer $u_0$ of the same parity as a root row $v_0$, and sample row $v$ at $u_v=u_0+(v-v_0)/h$. Along an edge from $v$ to $v+d^2$ the sample position changes by $d^2/h\equiv d\bmod 2h$. This preserves the required row parity and gives opposite secondary bits. Give isolated rows any secondary bit. Together with the primary bit these samples four-colour the 58-row square-difference graph, contradicting the certified $W(x^2;4)=58$.

## Two scalar distances in a common residue class

There is an additional constraint when $16\mid m$, $a$ is odd and $b=6a\bmod16$. Every class modulo 16 must contain both primary bits in the period word.

The signed normalized values at $-2$ and $6$ are $s=-2a+3b$ and $t=6a+15b$. Both are multiples of 16 and $t-5s=16a$. The quotients $s/16$ and $t/16$ have opposite parity, so $A=|s|$ and $D=|t|$ have different 2-adic valuations. Both are positive in the remaining coefficient range. The argument after horizontal reflection uses the values at $2,-6$ and gives the same absolute bounds.

If the primary bit is constant on a residue class $r\bmod16$, take $0\le r<16$ and $h=\gcd(A,D)$. Starting at $r$, visit the residues $r+(kA\bmod (A+D))$. This cycle has odd length $(A+D)/h$, and each edge has absolute distance $A$ or $D$. It stays in the chosen class and its maximum is $r+A+D-h\le A+D-1$. But $A+D\le(40p+8q)/g\le57(p+q)/g$, even with either choice of signs. The secondary bit could not alternate around this cycle. This proves the constraint. Its use after multiplication by an odd unit simply permutes the classes modulo 16.

## Finite certificates

For each remaining orientation and period, use one variable for each primary residue and one secondary variable for each even-sum vertex of a $15\times55$ rectangle. For each edge, forbid the four assignments in which its primary bits agree and its secondary bits also agree. If a single primary residue occurs at both ends, only secondary inequality is needed. The period and arithmetic constraints above are included. A satisfiable small rectangle triggers a second test on the $43\times58$ rectangle. Both fit inside the requested square.

The replay command below regenerates each refutation with Glucose and checks it with the separate drat-trim executable before proceeding. The full scalar words and their unrestricted second bits are never enumerated. Use the python-sat environment and drat-trim build from the [main reproduction instructions](README.md#reproduction-and-provenance).

~~~sh
PYTHONDONTWRITEBYTECODE=1 "$venvdir/bin/python" palette.py /tmp/q4-drat-trim
~~~

The run comprised 64 vertical orientations, 1,601 refutations on the smaller rectangle and four on the larger rectangle. The algebraic test of vertical orientations also covers $m=1$. The replay can be split with inclusive flags `--first` and `--last`; our two disjoint batches covered 1–19 and 20–64. [Encoder and proof replay](palette.py)
