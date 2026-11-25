# A finite decision problem for the target 57

The assertion $W(ex^2+fx;4)\le57(|e|+|f|)+1$ for all coefficients is decidable by a finite computation. The reduction below encodes the *actual scalar graph*, retaining all identifications around its circumference. The [winding proof](forcing.md) establishes the assertion directly. The state bound in the alternative decision procedure is large. We have checked the reduction on concrete coefficient pairs, but have not evaluated its full transition monoid.

## The cyclic strip

By sign symmetry, scaling and the cropped-rectangle bound it suffices to take coprime positive $p,q$ with $p>9q$, where $p$ is the quadratic coefficient. Number the scalar vertices from $0$ through $57(p+q)$ inclusive. Define the periodic binary word

$$b_u=\lfloor (u+1)q/p\rfloor-\lfloor uq/p\rfloor,\qquad u\in\mathbb Z/p\mathbb Z.$$

For column $u$ take the residue $r_u=qu\bmod p$ in $[0,p-1]$. Vertex $(u,k)$ represents $r_u+pk$. Its column height is

$$h_u=57+\sum_{i=1}^{57} b_{u-i}+\mathbf1_{u\equiv57\bmod p},\qquad 0\le k<h_u.$$

Indeed its integer lattice representative has second coordinate $v=k-\lfloor uq/p\rfloor$. The last allowed $v$ is $57-\lceil (u-57)q/p\rceil$. Subtracting the first allowed $v$ and adding one gives the formula. The indicator records equality at the final endpoint. Coprimality makes the column residues a permutation of $[0,p-1]$, so this is a bijection. Also $h_u\le\lfloor57(1+q/p)\rfloor+1\le64$.

For every $1\le d\le8$, join $(u,k)$ to the in-range vertices

$$\left(u+d\bmod p,\ k+\sum_{j=0}^{d-1}b_{u+j}\ \pm d^2\right).$$

The wraparound sum follows from the floor differences and remains valid across the column chosen as the origin. The integer labels differ by $qd\pm pd^2$. Conversely a scalar edge can be oriented to have exactly this signed difference. Its other column is forced by reduction modulo $p$. For $d\ge9$ the smaller absolute difference is at least $81p-9q>57(p+q)$ and increases with $d$. This proves equality of the strip graph and the scalar graph.

The implementation compares labelled edge sets against an independent direct enumeration of signed polynomial values. For a single scalar refutation it uses the largest residue class modulo $\gcd(p+q,2p)$, the gcd of all polynomial values. These values are integer combinations of $p+q$ and $2p$ by $pd^2+qd=(p+q)d+2p\binom d2$. The values at $1$ and $-1$ show the converse divisibility. [Encoder and cross-check](strip.py)

## Finite transition relations

Mark position zero once per period of $b$. There is a fixed finite automaton recognizing the marked cyclic words whose strips have a four-colouring.

* At each column, nondeterministically choose a height and up to 64 colours. Check the height from the preceding 57 bits and the mark 57 positions back.
* Check the new column against the preceding eight coloured columns using the displayed edge rule and the intervening bits. Keep their colours and heights, and the last 57 bits and marks, as state.
* Accept a cyclic word exactly when reading it once returns some state to itself.

Every colouring gives a closed state walk by periodic repetition. Conversely any closed state walk can be repeated indefinitely. After 57 or more steps its stored history consists entirely of actual choices along that walk. The checks then apply to every column and every wraparound edge, even if the period is less than 57. The closed walk assigns one set of colours per column of the period.

Let $R(w)$ be the relation on automaton states for an unmarked nonempty word $w$, and $S(w)$ the relation with precisely its first letter marked. Relations compose in reading order. The summary of a concatenation is

$$ (R(xy),S(xy))=(R(x)R(y),\,S(x)R(y)). $$

There are finitely many summaries. A coefficient word gives a counterexample precisely when $S(w)$ contains a diagonal pair.

## Enumerating all primitive slopes

Start with the neighbouring fractions $0/1$ and $1/9$, whose words are $0$ and $0^8 1$. For neighbouring fractions $q_1/p_1<q_2/p_2$ with $p_1q_2-p_2q_1=1$, insert their mediant. Its word is the concatenation of the parent words in that order.

For the first $p_1$ positions, the mediant floor at index $i$ differs in its argument from $iq_1/p_1$ by $i/(p_1(p_1+p_2))<1/p_1$, so the floors agree. For index $p_1+j$, the argument differs from $q_1+jq_2/p_2$ by $(p_2-j)/(p_2(p_1+p_2))<1/p_2$ for $0\le j\le p_2$. Both differences are nonnegative. Taking consecutive floor differences proves the word identity.

Every primitive slope in the open interval occurs this way. In a bracketing pair, its primitive denominator-numerator vector is $a(p_1,q_1)+b(p_2,q_2)$ for positive coprime integers $a,b$ by the determinant-one condition. If $a=b$ it is the mediant. Otherwise choosing the subinterval containing it subtracts the smaller coefficient from the larger until they coincide.

Traverse this binary tree using the ordered pair of parent summaries as key. For a new key, compose once for the mediant, test its marked diagonal, and enqueue the two child keys. Store representative parents to recover actual coefficients at the first accepting key. If a key repeats, its entire future sequence of tests depends only on that key. Thus the traversal terminates and either exhibits a counterexample or proves the target for every remaining coefficient. The pure-square case then gives equality $C_4=57$ in the latter event. A counterexample by itself would only raise the lower bound on the optimum.

The finite termination proof does not bound the transition computation by practical resources. In particular a time limit on a scalar SAT run cannot substitute for exhaustion of this traversal.

## A local consequence of the pure-square threshold

In a hypothetical sharp-target colouring for $p>9q>0$, there cannot be nine consecutive lattice columns sharing 57 consecutive rows on which the colour is constant along each row. This holds even when that condition is imposed on only the even-sum component. In particular a long region coloured by repeating a pure-square extremal word across columns cannot supply a boundary for a counterexample.

Use physical lattice coordinates, so a point is present when $0\le qu+pv\le57(p+q)$. Write the row block as $v_0+r$, $0\le r\le56$. In a putative nine-column block the common row colours form a square-difference-free word of length 57. For $d\le7$ there are at least two consecutive choices for the left endpoint column of a step of horizontal length $d$. One has the parity needed for either prescribed starting row.

After naming the colours in order of first appearance, there are exactly four such words. In 54 rows they coincide. The exceptions have indices 19, 28 and 37. Let $D_r$ be the set of colours occurring in row $r$ among the four words. For every $r$ and every colour outside $D_r$ there is an in-range row $r\pm d^2$ whose singleton set consists of that colour. For a new column this gives a neighbour in the column $d$ places earlier. Consequently, if the preceding seven columns obey these row sets, every new vertex in the block must also obey them while the 57 rows remain available. A standard-library exhaustive search and the direct row-set checks reproduce these facts. [Forcing check](stripe.py)

Let $U$ be the eighth of the nine given columns. Move right from $U$ to the first column $u$ of the correct parity where row $v_0-1$ is present. If its label is already nonnegative at $U$, the needed column is $U$ or $U+1$, both in the original block. Otherwise its label at entry is less than $2q$. The top row's label then differs by $57p$ and is still at most $57(p+q)$. Thus the 57 rows remain available from $U$ through entry. At $(u,v_0-1)$ the earlier neighbours in rows $r=d^2-1$ have singleton sets with colours covering all four choices, a contradiction.

~~~sh
python3 stripe.py
~~~

## Every rational comparison with the optimum is decidable

The same method decides $C_4\le A/B$ for any positive integers $A,B$ with $57\le A/B\le64$. In particular $C_4$ is a computable real. This statement concerns termination, independent of a resource estimate for a practical approximation.

For a primitive pair $(p,q)$, a violation means that the interval of length $\lfloor A(p+q)/B\rfloor+1$ has a proper four-colouring. Multiply **all distances** by $B$ and use instead the integer interval $[0,A(p+q)]$. Its residue class zero modulo $B$ is the original interval after division, and every other class embeds as a prefix. The two colouring questions are equivalent. The proved sharp-target regions suffice outside $p>9q>0$ for every comparison under consideration.

In the strip for this enlarged interval use $A$ in place of 57 in the height and marking formulas. The column heights are bounded by $\lfloor10A/9\rfloor+1$. The edge with parameter $d$ advances $Bd$ columns and changes row by the sum of the intervening $Bd$ bits plus or minus $Bd^2$. For $d\ge9$, already $81p-9q>64(p+q)$, so $1\le d\le8$ still suffices. The automaton now remembers $A$ bits and marks for the height calculation and $8B$ columns and intervening bits for the edge checks. These are constants for the chosen rational comparison. The coefficient words, mediants and relation-composition rule are unchanged. The finite traversal decides the comparison. Bisection of $[57,64]$ using these rational comparisons yields arbitrarily narrow certified enclosures in principle.

An explicit, very large witness bound follows even for the original target. Let $n=4^{57}(1+4+\cdots+4^{64})^8$. At most $n$ states are needed to store the histories. There are at most $K=2^{4n^2}$ ordered pairs of word summaries. If 57 fails, there is an accepting mediant reached within $K$ distinct parent keys, since any repeated key on a shortest accepting path can be skipped. Each subdivision increases the larger parent denominator by at most a factor of two. Thus some primitive counterexample then has $p\le9\cdot2^K$.

Two supplementary labelled-graph audits cover 29 primitive pairs for the first comparison below and three for the second. The latter includes column jumps longer than a whole period.

~~~sh
python3 strip.py audit 30 --target 115 2
python3 strip.py audit 12 --target 629 11
~~~

## The limiting worst ratio near the axis is an integer

Let $D$ be the limit, as $\eta$ decreases to zero, of the supremum of $(W(px^2+qx;4)-1)/(p+q)$ over primitive pairs with $0<q/p\le\eta$. These nested suprema give a well-defined number in $[0,64]$. Then $D$ is an integer.

Suppose instead that $k<D<k+1$, with $k\le63$. Fix $0<\delta<D-k$. There are pairs with $p/q$ arbitrarily large whose intervals $[0,L]$, $L=kp+s$ and $s=\lfloor\delta p\rfloor$, have a four-colouring. This follows from the definition of $D$ by choosing ratios bounded strictly above $k+\delta$. Choose $p/q$ large enough that $L<64p-8q$. Only steps with $d\le7$ occur.

In the cyclic strip, a column with residue $r=uq\bmod p$ has $k+1$ vertices if $r\le s$ and $k$ otherwise. Between successive wraps, $r$ increases in steps of $q$, starting below $q$. Each of the $q$ runs therefore has a block of high columns followed by a block of low columns. The high blocks have length at least $\lfloor(s+1)/q\rfloor$, which can be arbitrarily large. The last column of each run carries the rise bit.

Inside each high block, a cut after seven high columns has a boundary state consisting of the last seven coloured columns. There are at most $4^{7(k+1)}$ states. Take the blocks long enough to have two equal states at internal cuts in every block. Repeating the segment between those cuts preserves properness. Indeed an edge spans at most seven columns, all internal rise bits are zero, and the states match at the splice. The incoming and outgoing states at the ends of the original block are unchanged. Choose a common multiple of the $q$ positive repeat lengths. Thus we can insert the same number $t$ of high columns in every run, for arbitrarily large $t$.

The new cyclic strip is precisely that for
$$p'=p+tq,\qquad q'=q,\qquad s'=s+tq,\qquad L'=kp'+s'=L+(k+1)tq.$$
In fact run $j$ starts at column $\lceil jp/q\rceil$. Its new start is shifted by $jt$ and its first residue is unchanged. Each run gains $t$ high columns and the number of low columns stays fixed. Its rise remains at the end. Coprimality is preserved. Also $64p'-8q-L'\ge64p-8q-L>0$, so all constraints in the new scalar graph were covered by the splice. The colourable length $L'+1$ divided by $p'+q$ tends to $k+1$ as $t$ grows. This contradicts $D<k+1$. The argument also applies when $q$ is held fixed and the limsup is taken over primitive $p$ tending to infinity.

### An explicit near-axis lower bound of 52

The [universal bound](forcing.md) gives $D\le57$, and the construction below gives $D\ge52$. Set $q=5$, $p=5K+1$ and $K\ge98$. The certificate gives a proper colouring on $52p-455$ vertices. Dividing by $p+5$ and increasing $K$ proves the claim for positive linear coefficients.

Use the cyclic strip on the scalar labels $0,\ldots,52p-456$. In each of its five runs between consecutive wraps, the final 91 columns have height 51 and all earlier columns have height 52. Indeed the low columns have residues in $[p-455,p-1]$, and exactly 91 residues in this interval lie in each class modulo five. Each run has at least seven high columns.

The certificate lists the 52 row colours in every high column of a run. Each of its five high words avoids all square distances. For the low columns drop the last letter and perform the listed changes one at a time, holding each resulting 51-letter word (including the initial word) for seven columns. Fill any unused low columns with the final word. The longest list has 12 changes. Every intermediate word avoids squares and the final word equals the next run's high word with its first letter removed. This accounts for the wrap, where the physical bottom row decreases by one.

Every edge uses $1\le d\le7$, since $64p-8q$ exceeds the interval span. It crosses at most one change. At a change between two 51-letter words only one row changes colour, while the endpoints of an edge are in distinct physical rows. Consequently at least one of the two checked words gives both endpoint colours. At a boundary between heights both endpoint colours agree with the adjacent high word. This proves the construction for all the stated coefficients. The verifier also directly colours and tests 25,077, 30,017 and 64,857 scalar vertices in three sample instances. [Five words and changes](row-cycle.txt) · [Independent scalar checker](row_cycle.py)

There is a sharp limitation for this construction. Suppose each run has a block of nine consecutive columns with the same colour on each of its first 53 physical rows, and its other columns have at least 52 rows. The following necessary transition graph has no directed cycle, even if the intermediate columns are coloured arbitrarily. The nine columns realize all square constraints, leaving 44 possible 53-letter words up to colour names. For a transition from $A$ to $B$ the 52 common physical rows begin with the prefix of $A$ and end with the suffix of $B$. For each row start with its single prescribed colour. Enlarge its allowed set to all colours except those still fixed in some row at a square distance. Iterate to a fixed point. Any later column must obey these sets by induction using earlier neighbours. The reverse argument applies from the right. Keep a directed edge only if, for some permutation of the colour names, the two endpoints obey both tests. The 137 surviving ordered pairs form an acyclic graph. Every cyclic sequence would give a directed cycle, which rules out this 53-row construction. This upper limit assumes such a uniform block in every run.

~~~sh
python3 row_cycle.py --check-53
~~~

### An effective gap below 64

This splicing argument also decides the endpoint question $C_4=64$ by one rational comparison. Set $H=4^{448}$ and $\varepsilon=1/(H+10)$. Then
$$C_4=64\quad\text{or}\quad C_4\le64-\varepsilon.$$

If $C_4>64-\varepsilon$, take a primitive pair whose ratio exceeds that value. The sharp-target regions are excluded, and the bound $W-1\le64p-6q$ gives $p/q>(70-\varepsilon)/\varepsilon$. Restrict a colouring to $[0,63p+\lfloor p/2\rfloor]$, which fits since its length is less than $(64-\varepsilon)(p+q)$. Its span is less than $64p-8q$. Each run now has more than $H+8$ high columns, each of height 64. Two internal cuts after seven high columns agree, since there are at most $H$ states. The construction above with $k=63$ yields ratios arbitrarily close to 64, proving $C_4=64$. The finite rational comparison procedure can therefore distinguish these two possibilities in principle. The subsequent winding proof gives $C_4=57$ and hence the second branch.

## Scalar certificates in the open range

The target $W(px^2+x;4)\le57(p+1)+1$ holds for $10\le p\le15$. By scaling, this covers every $E=pF$ on these six rays. For odd $p$, the normalized component has step two and the encoding uses exactly one colour per vertex. For even $p$, the input orders vertices by lattice columns and requires at least one colour per vertex. The four edge clauses forbid all shared colours in either encoding, so selecting any assigned colour at each vertex gives a proper colouring.

Run the following from the problem directory after building the two pinned executables in the [reproduction instructions](README.md#reproduction-and-provenance). The audit compares every labelled edge on every primitive pair in its stated range. The six scalar CNFs are generated by direct signed distances. The largest binary proof in this run occupied 59 MB.

~~~sh
PYTHONDONTWRITEBYTECODE=1 python3 strip.py audit 65
sh replay_scalar.sh "$builddir/kissat/build/kissat" /tmp/q4-drat-trim
~~~

| $p$ | SHA-256 of the scalar DIMACS input | SHA-256 of the checked binary proof |
|---:|---|---|
| 10 | 6ee1fb3a12df617087c82124b71b63ee6b9243354ca845485b53a5bdc6c2390f | ff4a273593d88ac7c2b4ce22ad0869b8a9788e0f982275c06ed3f6cc612b9471 |
| 11 | 462dc99694513985e367d4cc42b8b9baac3963724643ebda7afb3907ba635b3c | 5a88a0df7c61569d77adb1431af07ab7abb3bafd428768f6dc45e2594eacacad |
| 12 | 7de5063763959f14370468ff478f26f4bf6ed744f9c538ab24c01ac1148f5b65 | ce1b080bb0c2a1e6218499a8a00d9cf94408f108d0c23677c24feacad0606389 |
| 13 | b97604ac5a6118e4fa440a41ac9aeb3c1a04a40ad47bb70d3fb6e68076a936b2 | 9b9a35b5c9b1e47c531cdf8ed6094c1619e09b9af19e664eaa2b0944f9e18f51 |
| 14 | 7717ca95cda214ba049d29d656296876681b0735d3023290289443cc03ecd181 | 575f1a9f48da524af77ab54bf919b620e9ac0e065f33bc5f95449c7cb35f7c8e |
| 15 | 8ffe2c4f19da45e0067cab47491249c6a79c55c70ad7403a8af80d163e185e5e | e0594937f64886a4c1220d8b2afe201fc027da903c5371f3c93b7540c488e02b |
