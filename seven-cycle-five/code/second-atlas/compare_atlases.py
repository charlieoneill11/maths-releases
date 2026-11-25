"""Compare the two independently generated atlases of 33-word codes up to G_3.

Stops with an error unless both lists have 1,016 classes, the two sets of
canonical forms are equal, the orbit sizes recorded in the first list agree
class by class with orbit sizes computed here from the images of the second
list's representatives, and these sizes add up to 16,672,544.
"""
import sys, itertools
from collections import Counter
import numpy as np

CODES = 16_672_544
GROUP = 16_464
classes_path, atlas_path = sys.argv[1], sys.argv[2]


def require(condition, message):
    if not condition:
        raise SystemExit('atlas comparison failed: ' + message)


def words_from_index(idx):
    return [(i // 49, (i // 7) % 7, i % 7) for i in idx]

codesA, sizesA = [], []
for line in open(classes_path):
    v = list(map(int, line.split()))
    require(len(v) == 34, 'malformed line in ' + classes_path)
    sizesA.append(v[0]); codesA.append(words_from_index(v[1:]))
codesB = []
for line in open(atlas_path):
    masks = list(map(int, line.split()))
    require(len(masks) == 7, 'malformed line in ' + atlas_path)
    w = [(u, bit // 7, bit % 7) for u, m in enumerate(masks) for bit in range(49) if m >> bit & 1]
    codesB.append(w)
require(len(codesA) == 1016 and len(codesB) == 1016, 'expected 1016 representatives in each list')

def near(x, y):
    return all(min((a - b) % 7, (b - a) % 7) <= 1 for a, b in zip(x, y))
for c in codesA + codesB:
    require(len(c) == 33 and len(set(c)) == 33, 'a representative does not have 33 distinct words')
    for x, y in itertools.combinations(c, 2):
        require(not near(x, y), 'a representative is not a code')

# all 16464 elements: perm, signs, translation
perms = list(itertools.permutations(range(3)))
signs = list(itertools.product((1, -1), repeat=3))
trans = np.array(list(itertools.product(range(7), repeat=3)))  # 343 x 3


def images(code):
    """The images of a code under all 16464 elements of G_3, as sorted index rows."""
    c = np.array(code)  # 33 x 3
    blocks = []
    for p in perms:
        cp = c[:, p]
        for s in signs:
            cs = (cp * np.array(s)) % 7  # 33x3
            allw = (cs[None, :, :] + trans[:, None, :]) % 7  # 343x33x3
            idx = allw[:, :, 0] * 49 + allw[:, :, 1] * 7 + allw[:, :, 2]
            idx.sort(axis=1)
            blocks.append(idx)
    rows = np.concatenate(blocks)
    require(rows.shape == (GROUP, 33), 'wrong number of group elements')
    return rows


def canon_and_orbit(code):
    """Lexicographically least sorted image, and the number of distinct images."""
    rows = images(code)
    order = np.lexsort(rows.T[::-1])
    least = tuple(int(v) for v in rows[order[0]])
    return least, len(np.unique(rows, axis=0))

canA = [canon_and_orbit(c) for c in codesA]
canB = [canon_and_orbit(c) for c in codesB]
setA, setB = {k for k, _ in canA}, {k for k, _ in canB}
print("classes A", len(setA), "classes B", len(setB), "equal sets:", setA == setB)
require(len(setA) == 1016 and len(setB) == 1016, 'two representatives in one list are equivalent')
require(setA == setB, 'the two lists define different classes')
print("sum of recorded orbit sizes (A):", sum(sizesA))
require(sum(sizesA) == CODES, 'recorded orbit sizes do not add up to 16672544')
require(all(n == s for (_, n), s in zip(canA, sizesA)), 'a recorded orbit size is wrong')
orbitA, orbitB = dict(canA), dict(canB)
require(orbitA == orbitB, 'orbit sizes differ between the two lists')
require(all(GROUP % n == 0 for n in orbitB.values()), 'an orbit size does not divide 16464')
stabilisers = Counter(GROUP // n for n in orbitB.values())
print("orbit sizes agree class by class; stabiliser orders", dict(sorted(stabilisers.items())))
require(stabilisers == {1: 1011, 2: 1, 3: 3, 6: 1}, 'unexpected stabiliser orders')
