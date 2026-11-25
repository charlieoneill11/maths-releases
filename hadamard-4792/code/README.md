# A real Hadamard matrix of order 4792

There exists a sign matrix $H$ of order $4792=8\cdot599$ satisfying $HH^{\mathsf T}=4792I$. The [compressed CSV](H4792.csv.gz) gives all 22,963,264 entries. The [certificate](certificate.json) specifies the same matrix using four strings of 1197 signs. The twelve hexadecimal masks below are a further lossless encoding.

## The witness

Take $G=\mathbb Z_7\times\mathbb Z_{19}\times\mathbb F_3^2$ with componentwise addition. Write points as $(x,y,u,v)$ in lexicographic order, with $v$ varying fastest. On the first two coordinates form the orbits of $(x,y)\mapsto(2x,4y)$ and sort the orbits by their least point. Their 17 representatives are

```text
(0,0) (0,1) (0,2) (1,0) (1,1) (1,2) (1,4) (1,5) (1,8)
(1,10) (3,0) (3,1) (3,2) (3,4) (3,5) (3,8) (3,10)
```

Choose a mask by the number of nonzero coordinates of $(u,v)$. In that mask, bit $j$, counted from the least significant bit starting at zero, gives the sign on orbit $j$. A set bit means $-1$ and a clear bit means $+1$.

| Block | At the origin | One nonzero | Both nonzero | Sign sum |
| --- | ---: | ---: | ---: | ---: |
| $A$ | `0c85b` | `1c32a` | `03cdc` | $1$ |
| $B$ | `08573` | `07c3c` | `187c2` | $1$ |
| $C$ | `08328` | `09e3d` | `16d4b` | $-1$ |
| $D$ | `04ad2` | `03e65` | `1991b` | $-1$ |

## Why these data give a Hadamard matrix

For each block $X$, let $D_X$ be its negative set, and put $N(t)=\sum_X|\{(g,h)\in D_X^2:g-h=t\}|$. The four sizes are $598,598,599,599$. Direct enumeration gives $N(0)=2394$ and $N(t)=1196$ for every one of the 1196 nonzero shifts. Expanding $x_X(g)=1-2\,1_{D_X}(g)$ gives

$$
\sum_X\sum_{g\in G}x_X(g)x_X(g+t)
=4\cdot1197-4\cdot2394+4N(t)
=\begin{cases}4788&t=0,\\-4&t\ne0.\end{cases}
$$

Let $m=1197$. Write $A,B,C,D$ also for their $m\times m$ group-developed matrices, with $X_{g,h}=x_X(h-g)$. Let $R_{g,h}=1$ when $h=-g$ and zero otherwise. The autocorrelation calculation gives $\sum_X XX^{\mathsf T}=4792I_m-4J_m$, where $J_m$ is all ones. Use the Goethals–Seidel array

$$
M=\begin{pmatrix}
 A&BR&CR&DR\\
 -BR&A&D^{\mathsf T}R&-C^{\mathsf T}R\\
 -CR&-D^{\mathsf T}R&A&B^{\mathsf T}R\\
 -DR&C^{\mathsf T}R&-B^{\mathsf T}R&A
\end{pmatrix}.
$$

The group is abelian, so the four developed matrices and their transposes commute. Using $RXR=X^{\mathsf T}$ and $R^2=I$ in the displayed array cancels the off-diagonal blocks of $MM^{\mathsf T}$. Its diagonal blocks all equal $\sum_X XX^{\mathsf T}$.

For $(a,b,c,d)=(1,1,-1,-1)$, the four sign sums, set

$$
S=\begin{pmatrix}a&b&c&d\\-b&a&d&-c\\-c&-d&a&b\\-d&c&-b&a\end{pmatrix},
\qquad
H=\begin{pmatrix}-S&S\otimes\mathbf1^{\mathsf T}\\
                   S\otimes\mathbf1&M\end{pmatrix},
$$

where $\mathbf1$ is the length-$m$ column of ones. Every entry of $H$ is a sign. We have $SS^{\mathsf T}=4I_4$. Writing $E=I_4\otimes\mathbf1$, the row sums in the displayed blocks give $ME=ES$. Thus the off-diagonal Gram blocks vanish. The upper diagonal block is $4(m+1)I_4$, and the lower one is $4I_4\otimes J_m+MM^{\mathsf T}=4792I_{4m}$. This proves the claim.

## Reproduce the exact checks

Run from this folder. The difference counter uses only the Python standard library. The matrix checker needs Python 3.10 or later and NumPy.

```sh
python3 verify_differences.py certificate.json --check-masks
python3 gram.py certificate.json 4792
```

The first command counts every directed difference and compares all 4788 signs with the masks. The second constructs every matrix entry and compares every pair of distinct rows by XOR and integer population count. All **11,479,236** distances are **2396**. Every row has 4792 signs and hence squared norm 4792.

Kishan Kumar’s unmodified general Spence builder independently reconstructed the same CSV. His standalone C checker reads the CSV, validates the entries and computes all 11,484,028 integer dot products on and above the diagonal. It found zero violations. The following commands check the included CSV with the pinned C source. [Upstream verifier](https://github.com/vatskishan03/Hadamard/tree/d885022144ba6bf4efa8315e14871a3736947527/verify)

```sh
curl -fsSLo check_matrix.c https://raw.githubusercontent.com/vatskishan03/Hadamard/d885022144ba6bf4efa8315e14871a3736947527/verify/check_matrix.c
cc -std=gnu11 -O3 -fopenmp check_matrix.c -o check_matrix
gzip -dc H4792.csv.gz | ./check_matrix
gzip -dc H4792.csv.gz | sha256sum
```

The canonical CSV has 57,400,980 bytes. Each entry is ASCII `1` or `-1`, commas separate entries, and every row ends with a single LF. Its SHA-256 is **`5953fc1f8ad4cfcd38c782b9e7be909af4b0d7dc5bd94073a98dc4765e57eab6`**. As corruption controls, swapping two unlike signs in a certificate block preserved its sign sum and caused both local checkers to reject it. Changing a single sign in the CSV produced 4791 violations in the standalone C checker.

## Search, attribution and order-5912 control

Kishan Kumar proposed this 36-element common multiplier group in §107 and constructed the order-5912 sister matrix in §108 using the odd-group form of Spence’s bordered array. Before the order-4792 search, we reproduced his order-5912 witness from seed 1002, round 33, instance 341. Independent reconstruction verified all 17,472,916 distinct row pairs and reproduced its published canonical CSV hash. [Kumar’s search record](https://github.com/vatskishan03/Hadamard/blob/d885022144ba6bf4efa8315e14871a3736947527/search/NOTES.md) · [Odd-group construction](https://github.com/vatskishan03/Hadamard/tree/d885022144ba6bf4efa8315e14871a3736947527/search/eightp) · [Order-5912 witness](https://github.com/vatskishan03/Hadamard/tree/d885022144ba6bf4efa8315e14871a3736947527/hadamard/5912)

At order 4792, the two prime-quotient screens retained 524 of 1141 normalized cases. The primary witness came from case 268 on the common multiplier $(2,4)$ on the first two factors and the four nonzero field squares on $\mathbb F_9$. The conditioned join processed 2,518,683 pair entries. A fresh compilation and replay of this case reproduced the same four strings. A second worker found a [separate certificate in case 523](certificate-case523.json). Both exact local checks pass for that certificate, omitting the primary-witness mask comparison. Its CSV SHA-256 is `f2dac720bb9f6e4ef13a22bb20e35b2baa5f0a5546c714aafaf4c619e2a717da`. The two matrices have not been classified up to equivalence. [Search measurements, source audit and replay commands](search-notes.md) · [Winning case record](winning-case.json)
