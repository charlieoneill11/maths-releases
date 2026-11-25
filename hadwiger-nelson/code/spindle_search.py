"""Find rooted Moser spindles whose other six points use only three old colors."""
import argparse
from itertools import combinations
import json
import math
from pathlib import Path
import numpy as np


def geometry():
    b=np.sqrt(3)
    u=np.exp(1j*np.arccos(5/6))
    return np.array([0,b,(b+1j)/2,(b-1j)/2,u*b,u*(b+1j)/2,u*(b-1j)/2])


def classifier(pattern):
    h=np.asarray(pattern['pieces'][0]['vertices'],float)
    U=float(pattern['period'][0][0]); y=.5
    sl=[]
    for mask in (h[:,0]<.1,h[:,0]>.8):
        q=h[mask]
        sl.append(q[np.argsort(q[:,1])])
    def classify(z):
        colors=np.zeros(z.shape,dtype=np.int32)
        margin=np.zeros(z.shape)
        for inc in (0,1):
            i=np.floor(z.real/U).astype(int)+inc
            t=z.imag/y-1.5*i
            j=np.floor(t).astype(int)
            py=(t-j)*y
            px=np.abs(z.real-i*U)
            l,r=[np.interp(py,q[:,1],q[:,0]) for q in sl]
            clearance=np.minimum.reduce([px-l,r-px,py,y-py])
            use=clearance>0
            colors[use]=1+3*inc+(-j[use])%3
            margin[use]=clearance[use]
        return colors,margin
    return classify


def run(pattern,patches,n_angles):
    classify=classifier(pattern)
    shapes=geometry();theta=2*np.pi*np.arange(n_angles)/n_angles
    R=np.exp(1j*theta)
    triples=list(combinations(range(1,7),3))
    output=[]
    for box in patches:
        l,r,b,t=map(float,box)
        p=((l+r)+1j*(b+t))/2
        best={}
        for k in range(7):
            offsets=np.delete(shapes-shapes[k],k)[:,None]*R[None,:]
            col,mar=classify(p+offsets)
            masks=np.bitwise_or.reduce(1<<col,axis=0)
            worst=mar.min(axis=0)
            for triple in triples:
                mask=sum(1<<c for c in triple)
                yes=np.flatnonzero(masks==mask)
                if len(yes)==0:continue
                pos=yes[worst[yes].argmax()]
                score=worst[pos]
                if triple not in best or score>best[triple][0]:
                    turn=round(math.tan(theta[pos]/2)*10**9)
                    best[triple]=(score,{'palette':list(triple),'root':k,'turn':turn,
                                         'labels':col[:,pos].tolist()})
        output.append({'box':box,'witnesses':[v[1] for v in best.values()]})
        print(box,len(best),[(tuple(e[1]['palette']),round(e[0],5)) for e in best.values()])
    return output


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--angles',type=int,default=32768)
    p.add_argument('--output',default='spindles.json')
    a=p.parse_args()
    boxes=[q['box'] for q in json.load(open('kempe_cycles.json'))['patches']]
    boxes.append(['-0.0001','0.0001','-0.0001','0.0001'])
    sets=run(json.load(open('parts_refined.json')),boxes,a.angles)
    Path(a.output).write_text(json.dumps(sets,indent=2)+'\n')
