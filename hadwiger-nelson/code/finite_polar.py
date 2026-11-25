"""Certify a finite-order bound using polar separation of nearby representatives.

Default replay uses the independently recorded edge-probability bounds. Add
--geometry to re-integrate the selected profile. No floating comparisons
enter the proof.
"""
import argparse
from fractions import Fraction as F
from functools import cache
from hashlib import sha256
import json
from pathlib import Path

from finite_extension import evaluation
from refit_wave_check import Hole
from wave_independent import check as edge_probabilities


@cache
def annulus(lo,hi):
    # Normalization divides all distances by twice the representative radius.
    l,r = F(lo,100),F(hi,100)
    assert 1 <= l <= r
    def cosine(a,b):
        return (a*a+b*b-1)/(2*a*b)
    upper = max(cosine(a,b) for a in (l,r) for b in (l,r))
    if upper >= 1:
        return 10000   # The disk packing bound is independently imposed below.
    for k in range(4,128):
        angle = F(44,7*(k+1))
        lower = 1-angle**2/2+angle**4/24-angle**6/720
        if lower > upper:
            return k
    return 10000


@cache
def ring_count(top):
    return min([annulus(100,top)]+[annulus(100,cut)+annulus(cut,top)
                                  for cut in range(110,top,10)])


def neighbours(t,a):
    if t<=a:return 0
    ratio=t/a
    disk=((1+2*ratio)**2)//1-1
    # Within the usage range, the coarse fallback for an unbounded annulus
    # count exceeds the independently proved disk bound.
    assert ratio<4 and disk<10000
    return min(disk,ring_count(-((-100*ratio)//1)))


def credits(hole,a,w,steps,short_steps):
    delta=w/steps
    B=L=0
    h=F(1)
    for i in range(1,steps+1):
        t=i*delta
        h=min(h,hole.overlap(t,t*t/2))
        B+=h*delta
        L+=h*delta*neighbours(t,a)/2
    C=F(0)
    for i in range(short_steps):
        u,v=F(i,short_steps),F(i+1,short_steps)
        dx=2*a*(1-u*u)/(1+u*u)
        dy=4*a*v/(1+v*v)
        C+=hole.overlap(dx,dy)*2*(v-u)/(1+v*v)
    down=lambda x:F(x*10**15//1,10**15)
    return down(C*F(7,11)),down(B*F(7,11)),-down(-L*F(100,157))


def run(path,cert_file,steps,short_steps,radii,geometry):
    spec=json.loads(path.read_text())
    digest=sha256(path.read_bytes()).hexdigest()
    raw=json.loads(cert_file.read_text())
    if isinstance(raw,list):
        raw=next(v for v in raw if v['file']==path.name)
        q,p,bins=F(raw['blank']),F(raw['common_probability']),raw['bins']
    else:
        q,p,bins=F(raw['blank']),F(raw['unit_conflict_upper']),raw['angular_bins']
    assert digest==raw['sha256']
    if geometry:
        ints=edge_probabilities(spec,bins)
        assert F(ints['blank'])==q and F(ints['conflict'])<=p
    left=spec['left']
    assert all(a[0]<b[0] for a,b in zip(left,left[1:]))
    assert left==[[5*10**11-t,v] for t,v in reversed(left)]
    hole=Hole(spec)
    w=F(73,10000)
    best=None
    for a in radii:
        c=credits(hole,a,w,steps,short_steps)
        lo,hi=9000,12500
        while hi-lo>1:
            n=(lo+hi)//2
            result=evaluation(n,None,q,p,a,c)
            if result and F(result['upper'])<1:
                lo=n
            else:hi=n
        result=evaluation(lo,None,q,p,a,c)
        if result and F(result['upper'])<1 and (best is None or (lo,-F(result['upper']))>
            (best['vertices'],-F(best['upper']))):best=result
    assert best
    return dict(profile=path.name,sha256=digest,angular_bins=bins,blank=str(q),unit_conflict_upper=str(p),
                cone_width=str(w),credit_bins=steps,short_credit_bins=short_steps,verified=best)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,default=Path('wavy_optimized.json'))
    p.add_argument('--edge-certificate',type=Path,default=Path('wave_order.json'))
    p.add_argument('--radii',type=F,nargs='+',default=[F(277,100000)])
    p.add_argument('--steps',type=int,default=2048)
    p.add_argument('--short-steps',type=int,default=2048)
    p.add_argument('--geometry',action='store_true')
    args=p.parse_args()
    print(json.dumps(run(args.profile,args.edge_certificate,args.steps,args.short_steps,args.radii,args.geometry),indent=2))
