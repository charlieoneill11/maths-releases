# A Hadamard matrix of order 4792

**Result.** There is a Hadamard matrix of order 4792 = 8 · 599: a 4792 × 4792 matrix H with entries ±1 and HHᵀ = 4792 I. No Hadamard matrix of this order was known before. The order is twice 2396, the smallest order for which no Hadamard matrix is known, and it was one of the last two open orders of the form 8p below 10,000; the other is 5752 = 8 · 719. Order 2396 itself remains open.

- Paper: [hadamard-4792.pdf](hadamard-4792.pdf). The LaTeX source is in [paper/](paper/) and builds with `pdflatex main.tex`, run twice.
- Matrix and certificate: [code/H4792.csv.gz](code/H4792.csv.gz) holds all 22,963,264 entries, and [code/certificate.json](code/certificate.json) gives the four sign sequences it is built from.
- Programs: [code/](code/). The construction notes are in [code/README.md](code/README.md) and the search record is in [code/search-notes.md](code/search-notes.md).
- Figure: the paper's picture of the matrix is drawn from the CSV file by [code/make_figure.py](code/make_figure.py), which needs NumPy and Pillow.

## The construction

H is a Goethals–Seidel array with a border, built from four ±1 functions a, b, c, d on the abelian group G = ℤ₇ × ℤ₁₉ × 𝔽₉ of order 1197. Their periodic autocorrelations sum to −4 at every nonzero element of G, and the paper's Theorem 3 shows that this makes H a Hadamard matrix of order 4(1197 + 1) = 4792. The four functions are constant on the 51 orbits of a group of multipliers of order 36, so twelve 17-bit masks describe them (the paper's Table 1).

The proof uses no outside theorems. It is the short argument for the bordered array, given in full in the paper, together with a finite count of differences.

## Checking the result

From `code/`, with Python 3.10 or newer and NumPy:

```sh
python3 verify_differences.py certificate.json --check-masks   # the autocorrelation identity (standard library only)
python3 gram.py certificate.json 4792                          # all 11,479,236 pairs of distinct rows
python3 check_array.py H4792.csv.gz                            # rebuild from the masks, H Hᵀ and the CSV's Gram matrix
gzip -dc H4792.csv.gz | sha256sum
```

The uncompressed CSV has 57,400,980 bytes and SHA-256 `5953fc1f8ad4cfcd38c782b9e7be909af4b0d7dc5bd94073a98dc4765e57eab6`. Kishan Kumar's standalone C checker also reads it and finds no violations; [code/README.md](code/README.md) gives the commands. Each check takes a few seconds.

A second solution, from another case of the search, is in [code/certificate-case523.json](code/certificate-case523.json). It passes the first two checks. We have not tested whether the two matrices are equivalent.

## How it was found

The functions were found by a computer search on ordinary CPUs, in a family of symmetric structures that Kishan Kumar identified for this order in his [search notes](https://github.com/vatskishan03/Hadamard/blob/d885022144ba6bf4efa8315e14871a3736947527/search/NOTES.md). He used the same construction for his Hadamard matrix of order 5912 = 8 · 739. The paper's Section 5 and [code/search-notes.md](code/search-notes.md) describe the search and how to replay it. The correctness of the result does not depend on the search.

## Citing

```bibtex
@misc{hadamard-4792-2026,
  author       = {O'Neill, Charles and Kirkby, Max and {Astra}},
  title        = {A {H}adamard matrix of order 4792},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://charlieoneill11.github.io/maths-releases/hadamard-4792/}},
  note         = {Preprint. Programs and data: \url{https://github.com/charlieoneill11/maths-releases/tree/main/hadamard-4792}},
}
```
