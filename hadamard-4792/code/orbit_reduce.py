"""Deduplicate K-level quadruples under common scalars, signs, reversals and block permutations."""
import numpy as np


def representatives(u, labels):
    if not len(u):
        return np.empty(0,dtype=np.int64)
    coords = np.array([np.argwhere(labels==o)[0] for o in range(17)])
    i,j = coords.T
    flip=labels[-i%7,-j%19]
    seen=set()
    permutations=[]
    for a in range(1,7):
        for b in range(1,19):
            p=labels[a*i%7,b*j%19]
            reverse=p[flip]
            pair=tuple(sorted((tuple(p),tuple(reverse))))
            if pair not in seen:
                seen.add(pair)
                permutations.append((p,reverse))
    # Coding uses three bits per letter. A global sign negation reverses
    # the six-letter order. The minimization runs independently per block.
    alphabet=np.array([-9,-7,-1,1,7,9],dtype=np.int8)
    place=8**np.arange(16,-1,-1,dtype=np.uint64)
    maxword=5*place.sum()
    indices={}
    for first in range(0,len(u),2048):
        digits=np.searchsorted(alphabet,u[first:first+2048]).astype(np.uint64)
        best=None
        for p,q in permutations:
            x=digits[:,:,p] @ place
            y=digits[:,:,q] @ place
            key=np.sort(np.minimum(np.minimum(x,maxword-x),np.minimum(y,maxword-y)),axis=1)
            if best is None:
                best=key
            else:
                diff=best!=key
                where=np.argmax(diff,axis=1)
                take=key[np.arange(len(key)),where]<best[np.arange(len(key)),where]
                best[take]=key[take]
        for i,row in enumerate(best):
            indices.setdefault(row.tobytes(),first+i)
    return np.array(list(indices.values()),dtype=np.int64)
