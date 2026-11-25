"""Check mixed shifts for every permitted lift of one joint projection node."""
import argparse
from itertools import product
import json
from pathlib import Path
from random import Random

import numpy as np
from joint import orbit_table
from lift import check_margins, field_array, lifts, paf_check


def mixed_shifts(generator):
    seen = set()
    shifts = []
    for i, j in product(range(1,7), range(1,19)):
        if (i, j) not in seen:
            shifts.append((i,j))
            seen.update((s*i*pow(2,t,7)%7, s*j*pow(generator,t,19)%19)
                        for t in range(9) for s in (-1,1))
    return shifts


def shift_counts(labels, shifts):
    n = int(labels.max()+1)
    matrices = []
    for shift in shifts:
        destinations = np.roll(labels, shift, (0,1))
        count = np.bincount((n*labels+destinations).ravel(), minlength=n*n)
        matrices.append(count.reshape(n,n).astype(np.int16))
    return matrices


def signature(masks, n, matrices):
    bits = np.arange(n)
    a, b, c = [2*((masks[:,k,None] >> bits) & 1).astype(np.int16)-1 for k in range(3)]
    channels = (a+4*b+4*c, a+b-2*c, a-2*b+c)
    return np.column_stack([((x @ mat)*x).sum(axis=1) for x in channels for mat in matrices])


def find_match(groups, wanted):
    # Exact 64-bit homomorphism used only for rejection. All collisions are examined.
    # Sorting the smaller pair list saves memory. Indexing is local to its cost tuple.
    order = sorted(range(4), key=lambda k:len(groups[k][0]))
    pairs = [(order[0],order[3]), (order[1],order[2])]
    pairs.sort(key=lambda p:len(groups[p[0]][0])*len(groups[p[1]][0]))
    (i,j),(k,l) = pairs
    a,b,c,d = [groups[x][0] for x in (i,j,k,l)]
    hashes = (a[:,None]+b).ravel()
    perm = np.argsort(hashes)
    hashes = hashes[perm]
    for start in range(0, len(c), max(1, 200000//len(d))):
        chunk = c[start:start+max(1,200000//len(d))]
        seek = (wanted-chunk[:,None]-d).ravel()
        left = np.searchsorted(hashes, seek)
        right = np.searchsorted(hashes, seek, side="right")
        for pos in np.flatnonzero(left < right):
            s,t = divmod(int(pos), len(d))
            for h in perm[left[pos]:right[pos]]:
                u,v = divmod(int(h), len(b))
                ix = [None]*4
                for key,val in zip((i,j,k,l),(u,v,start+s,t)):
                    ix[key] = groups[key][1][val]
                yield ix


def full_certificate(labels, masks):
    blocks = []
    for row in masks:
        signs = 2*((row >> np.arange(labels.max()+1)[:,None]) & 1)-1
        blocks.append(field_array(signs, labels))
    try:
        paf_check(np.array(blocks), lambda s: (4792 if not any(s) else 0)-4)
    except ValueError:
        return None
    return dict(order=4792, construction="spence", group=[7,19,3,3],
                sequences=["".join("+" if x == 1 else "-" for x in b.ravel()) for b in blocks])


def complete(data):
    labels, blocks = lifts(data)
    check_margins(data, labels)
    shifts = mixed_shifts(data["generator"])
    matrices = shift_counts(labels, shifts)
    rng = Random(599)
    weights = np.array([rng.getrandbits(64) for _ in range(3*len(shifts))], dtype=np.uint64)
    target = np.array([-36]*len(shifts)+[0]*(2*len(shifts)), dtype=np.int64)
    wanted = target.astype(np.uint64) @ weights

    cost_tuples = [cs for cs in product(*(np.unique(cost) for _,cost in blocks)) if sum(cs)==528]
    groups = []
    for i, (triples,cost) in enumerate(blocks):
        choices = {}
        for w in sorted({cs[i] for cs in cost_tuples}):
            rows = triples[cost == w]
            hashes = []
            for start in range(0,len(rows),4096):
                sig = signature(rows[start:start+4096], int(labels.max()+1), matrices)
                hashes.append(sig.astype(np.uint64) @ weights)
            choices[w] = (np.concatenate(hashes), rows)
        groups.append(choices)
    collisions = 0
    for cs in cost_tuples:
        for solution in find_match([groups[i][c] for i,c in enumerate(cs)], wanted):
            collisions += 1
            cert = full_certificate(labels, solution)
            if cert:
                return len(cost_tuples), collisions, cert
    return len(cost_tuples), collisions, None


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("node", type=Path)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    count, collisions, certificate = complete(json.loads(args.node.read_text()))
    print(f"{count} feasible cost tuples, {collisions} hash matches, full solution {certificate is not None}")
    if certificate is not None:
        if args.output:
            args.output.write_text(json.dumps(certificate)+"\n")
        else:
            print(json.dumps(certificate))
