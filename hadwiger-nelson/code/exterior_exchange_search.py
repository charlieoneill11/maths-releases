"""Search two-hole switch chains that meet inside an earlier exterior witness.

Each old witness chain is two rational unit steps S -> R -> Z. When chains
from different A holes have overlapping second images, work backwards from
a common square in the overlap. Switching these five cells lets both R's
use Z's old color while Z changes to a further color. Remaining conflicting
points are erased. Supports the six original colors and a finite collar.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
import json
import math
from pathlib import Path
from adaptive_recolor import SOURCES, quarter, translate, unit
from verify import read_point


def intersection(a,b):
    x,X=max(a[0],b[0]),min(a[1],b[1])
    y,Y=max(a[2],b[2]),min(a[3],b[3])
    return (x,X,y,Y) if x<X and y<Y else None


def row_label(c,j):
    return 1+3*((c-1)//3)+(c-1-j)%3


def records(pattern,old):
    u,v=map(read_point,pattern['period'])
    W,H=u[0],F('0.5')
    for l,entry in enumerate(old):
        if 'choices' not in entry:continue
        source=SOURCES[0]
        for k in entry['path']:source=quarter(source,k)
        for color,(step,stops) in enumerate(entry['choices'],1):
            v1=unit(step)
            first=translate(source,v1)
            for c2,step2 in zip([c for c in range(1,7) if c!=color],stops):
                v2=unit(step2)
                last=translate(first,v2)
                m0=math.ceil(-last[1]/W)
                m1=math.floor((W-last[0])/W)
                for m in range(m0,m1+1):
                    n0=math.ceil((-last[3]-m*u[1])/H)
                    n1=math.floor((H-last[2]-m*u[1])/H)
                    for n in range(n0,n1+1):
                        off=(m*W,m*u[1]+n*H)
                        box=intersection(translate(last,off),(F(0),W,F(0),H))
                        if box:
                            yield dict(leaf=l,source_shift=[m,n],c=row_label(color,n),
                                       d=row_label(c2,n),v=v1,w=v2,endpoint=box,
                                       witness1=step,witness2=step2)


def cells(pair):
    a,b=pair
    rect=intersection(a['endpoint'],b['endpoint'])
    if not rect:return
    x,X,y,Y=rect
    # Use a square to simplify the shape/density comparison. Remove 2% in
    # width so each closed cell lies in the open certificate rectangle.
    side=min(X-x,Y-y)*F(49,50)
    if side<F(1,1000000):return
    z=((x+X)/2,(y+Y)/2)
    diff=lambda p,q:tuple(t-s for t,s in zip(p,q))
    r=[diff(z,k['w']) for k in pair]
    s=[diff(p,k['v']) for p,k in zip(r,pair)]
    p=[*s,*r,z]
    for k,h in combinations(range(5),2):
        if all(abs(i-j)<=side for i,j in zip(p[k],p[h])):return
    return side,p


def distance_square(p,q,side):
    d=[abs(a-b) for a,b in zip(p,q)]
    return (sum(max(0,t-side)**2 for t in d),sum((t+side)**2 for t in d))


def serialize(a):
    return {k:a[k] for k in ['leaf','source_shift','c','d','witness1','witness2']}


def geometries(pattern,old):
    stocks=list(records(pattern,old))
    bins=defaultdict(list)
    geom=[]
    for k,rec in enumerate(stocks):
        x,X,y,Y=rec['endpoint']
        keys=list(product(range(int(100*x),int(100*X)+1),range(int(100*y),int(100*Y)+1)))
        for h in {i for key in keys for i in bins[key]}:
            prior=stocks[h]
            if rec['source_shift']==prior['source_shift'] or rec['d']!=prior['d']:continue
            pair=(rec,prior)
            got=cells(pair)
            if not got:continue
            side,centers=got
            eligible=[]
            for e in range(1,7):
                if e==rec['d']: continue
                labels=[rec['c'],prior['c'],rec['d'],rec['d'],e]
                if any(labels[i]==labels[j] and lo<1<hi for i,j in combinations(range(5),2)
                       for lo,hi in [distance_square(centers[i],centers[j],side)]):continue
                eligible.append(labels)
            if eligible:geom.append((side,centers,pair,eligible))
        for key in keys:bins[key].append(k)
    if not geom:raise ValueError('No compatible branched witness pairs')
    return len(stocks),geom


def run(pattern,old):
    import numpy as np
    from spindle_search import classifier
    nstocks,geom=geometries(pattern,old)
    classify=classifier(pattern)
    theta=(np.arange(512)+.5)*2*np.pi/512
    circle=np.exp(1j*theta)
    weights=abs(circle.real)+abs(circle.imag)
    choices=[]
    for side,centers,pair,eligible in geom:
        zz=np.array([float(x)+1j*float(y) for x,y in centers])[:,None]
        labels,_=classify(zz+circle)
        for colors in eligible:
            # First-order length of circle/tile intersections, weighted
            # by the width of a translated square in the radial direction.
            # Used only to rank, not to certify any area or exclusion.
            score=float((weights*(labels==np.asarray(colors)[:,None])).sum()*2*np.pi/len(theta))
            choices.append((score/float(side),side,centers,pair,colors))
    choices.sort(key=lambda r:r[0])
    separation=lambda record: math.dist([float(t) for t in record[2][0]],
                                        [float(t) for t in record[2][1]])
    nearest=min(separation(record) for record in choices)
    nearby=[record for record in choices if separation(record)<nearest+.02]
    out=[]
    for score,side,centers,pair,colors in choices[:30]+nearby[:5]:
        out.append(dict(first_order_cost_per_cell=score,side=str(side),
                        centers=[[str(x),str(y)] for x,y in centers],labels=colors,
                        chains=list(map(serialize,pair))))
    return dict(lifted_witness_boxes=nstocks,branched_geometries=len(geom),
                compatible_colorings=len(choices),nearest_hole_separation=nearest,
                near_options=len(nearby),shortlist=out)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('output',type=Path)
    p.add_argument('--pattern',type=Path,default=Path('parts64.json'))
    p.add_argument('--witnesses',type=Path,default=Path('adaptive_annuli_wide.json'))
    args=p.parse_args()
    result=run(json.loads(args.pattern.read_text()),json.loads(args.witnesses.read_text()))
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print({k:v for k,v in result.items() if k!='shortlist'})
