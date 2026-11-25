# Multiplicities on the complete atlas of 33-site supports

Every axis of a cap-nine 106-word packing uses **at least 59 distinct suffixes**. At most **32** suffixes have multiplicity at least two, and at most **15** have multiplicity three. Thus at least **28** used suffixes lie outside any given projected 31-band on the same axis.

Choose one height axis. A suffix of multiplicity three is isolated from all other used suffixes, because its three mutually separated heights dominate the seven-cycle. All suffixes with multiplicity at least two form an independent set in three dimensions. Two conflicting suffixes of that kind would need four separated heights between them.

## Maximum independent sets in three dimensions

The native enumeration first checks the planar ceiling of ten. The 980 planar ten-sets have three isometry classes. In a three-dimensional 33-set, let \(d_i\) be ten minus the number of words on two adjacent levels starting at \(i\). The seven deficits sum to four, and the level at \(i\) has \(3+d_{i+1}+d_{i+3}+d_{i+5}\) words. For a putative 34-set, the deficit sum is two and the constant in the level formula is four. Translate and reflect the sequence of deficits to its least cyclic image, so the first pair of levels forms a ten-set. Normalize that planar ten-set, then enumerate every allocation of its sites to the first two levels and every compatible sequence of further planar layers of the prescribed sizes.

A two-dimensional dynamic program bounds each transverse window by the number of sites already present plus the maximum that fits in the free rows between its fixed boundary rows. On each axis the seven windows must sum to twice the target. The program exhausts the 34-site search with no solutions and produces **1,016 isometry classes of 33-sets**. It counts all motions to a canonical representative to recover orbit sizes. They sum to **16,672,544** labeled maximum sets, reproducing the historical atlas. The sorted representatives in `atlas.tsv` are used by both price checks.

## Bounding triples

Adjoin all triple suffixes to each of the seven projected adjacent bands. The result stays independent. Every triple was absent from exactly one band, so the augmented sizes sum to \(212+T\), where \(T\) is the number of triples. If \(T\ge16\), this sum exceeds \(7\cdot32\) and some augmented support is a maximum 33-set \(A\). All its sites are physically used, and it contains every triple.

Write \(t_p\) for the triple indicator on \(A\), zero elsewhere. The residual multiplicity \(r_p\) is zero at a triple and at most two everywhere else. Total mass is \(\sum_p(r_p+3t_p)=106\). Every site of \(A\) satisfies \(r_p+t_p\ge1\), and every site satisfies \(r_p+2t_p\le2\). A unit suffix cube has mass at most three. A strip fixing two suffix coordinates to adjacent pairs has mass at most nine, and a single-coordinate band has mass at most 31. For each atlas entry, the supplied integer prices contradict these inequalities at \(T\ge16\). Where needed the proof branches on the two values of a triple indicator. Thus \(T\le15\).

## Bounding doubles and triples together

Their suffixes form an independent set of size at most 33. At equality they are precisely some maximum set \(A\). The physical multiplicity at site \(p\) then has the form \(2\,\mathbf{1}_{p\in A}+z_p\), where \(z_p\) is a bit on every site of the torus. To reach size 106 these bits must sum to at least 40. Each cube, strip and band again bounds its total mass. Integer prices and branches on individual bits exclude all 1,016 cases, proving that at most 32 sites have multiplicity two or three.

Every used suffix contributes one word, every double or triple contributes one more, and every triple contributes a third. The number of used suffixes is therefore at least \(106-32-15=59\).

## Replay

Run in this directory with assertions enabled. The native program regenerates the atlas. The standard-library verifier checks each representative's independence, covers every zero/one branch in both families of certificates and checks each contradiction using integer arithmetic. At a leaf it combines the priced inequalities. The minimum of the combined left side on the assigned unit box strictly exceeds the combined right side.

```sh
g++ -std=c++17 -O3 atlas.cpp -o /tmp/c7-atlas33
/tmp/c7-atlas33 > /tmp/c7-atlas33.tsv
cmp atlas.tsv /tmp/c7-atlas33.tsv
python3 verify.py
```
