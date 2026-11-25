"""Rational certificate for a wavy partial labeling with rare unit-edge conflicts.

All lengths use integers scaled by SCALE. This upper bounds failure for a
FINITE configuration; the plane labeling itself may have unit conflicts.
"""
import argparse
from bisect import bisect_right
from fractions import Fraction as F
from itertools import pairwise
import json
from pathlib import Path

SCALE=10**12
PI_LOW=F(314159,100000)


def ceildiv(a,b):
    return -((-a)//b)


def signed_eval(seg,h,up):
    a,b,p,q=seg
    num=p*(b-h)+q*(h-a)
    return ceildiv(num,b-a) if up else num//(b-a)


def segments(points):
    return [(a,b,p,q) for (a,p),(b,q) in pairwise(points)]


def positive_integral2(a,b,w):
    if min(a,b)>=0:return (a+b)*w
    if max(a,b)<=0:return 0
    return ceildiv(max(a,b)**2*w,abs(a-b))


def area_upper2(L,R,lv,rv,dx,dy,diam,k_num,k_den,H):
    """Upper double area for dx >= dx0 and dy in [dy0,dy0+diam]."""
    if dy>=H:return 0
    s=bisect_right(rv,dy)-1
    t=0;lo=dy;total=0
    margin=ceildiv(diam*k_num,k_den)
    while lo<H:
        u=R[s];v=L[t]
        hi=min(u[1],v[1]+dy)
        # Both 0 and the affine L(s-dy)-K*diam are lower bounds for
        # the actual left edge, wherever the true overlap exists. Choose
        # one affine function for this WHOLE interval. Endpoint bounds
        # then extend by linearity before taking the positive part.
        a=signed_eval(v,lo-dy,False)-margin
        b=signed_eval(v,hi-dy,False)-margin
        if a+b<0:
            a=b=0
        aa=signed_eval(u,lo,True)-a-dx
        bb=signed_eval(u,hi,True)-b-dx
        total+=positive_integral2(aa,bb,hi-lo)
        lo=hi
        if u[1]==hi:s+=1
        if v[1]+dy==hi:t+=1
    return total


def read(spec):
    x=spec['x'];L=spec['left'];R=spec['right'];H=SCALE//2
    assert type(x)==int and F(91,100)*SCALE<x<F(94,100)*SCALE
    for p in [L,R]:
        assert all(type(c)==int for pair in p for c in pair)
        assert all(a[0]<b[0] for a,b in pairwise(p)) and p[0][0]==0 and p[-1][0]==H
        assert {(a,b) for a,b in p}=={(H-a,b) for a,b in p}
    assert all(0<=l<=SCALE//20 for _,l in L)
    assert all(8*SCALE//10<=r<SCALE for _,r in R)
    assert {(a,r) for a,r in R if a<=H//2}=={(a-H//2,2*x-r) for a,r in R if a>=H//2}
    # These checks give disjoint master strips across the lattice and ensure
    # near-contact offsets have dx larger than either side's oscillation.
    return x,L,R


def certify(spec,N=16384):
    x,left,right=read(spec);H=SCALE//2
    L,R=map(segments,(left,right))
    K=max(F(abs(b-a),v-u) for u,v,a,b in L)
    lv=[u for u,v,a,b in L]+[H]; rv=[u for u,v,a,b in R]+[H]
    blank=F(sum((b-a)*(p+q) for a,b,p,q in L),2*x*H)
    xmax=max(r for _,r in right)
    quad=0
    def endpoints(j):
        d=N*N+j*j
        return (SCALE*(N*N-j*j),2*SCALE*N*j,d)
    prev=endpoints(0)
    for j in range(N):
        cur=endpoints(j+1)
        a=cur[0]//cur[2];b=ceildiv(prev[0],prev[2])
        c=prev[1]//prev[2];d=ceildiv(cur[1],cur[2])
        prev=cur
        area=0
        # Only these two positive-area overlaps are possible in quadrant I.
        for dx,dylo,dyhi in [(a,c,d),(2*x-b,c-3*SCALE//4,d-3*SCALE//4)]:
            dy=max(0,dylo,-dyhi); top=max(abs(dylo),abs(dyhi))
            if dx<xmax and dy<H:
                area+=area_upper2(L,R,lv,rv,dx,dy,top-dy,K.numerator,K.denominator,H)
        # Upper Darboux bin bound after the t=tan(theta/2) substitution.
        quad+=ceildiv(area*N,N*N+j*j)
    bad=2*F(quad,x*H)/PI_LOW
    return blank,bad


def rationalize(source):
    x=round(float(source['x'])*SCALE)
    def front(points,top):
        return [(round(float(a)*SCALE),round(float(b)*SCALE)) for a,b in points if a<=top+1e-14]
    l=front(source['L'],.25)
    if l[-1][0]!=SCALE//4:
        l.append((SCALE//4,0))
    r=front(source['R'],.125)
    r[-1]=(SCALE//8,x)
    r=r+[(SCALE//4-a,2*x-b) for a,b in r[-2::-1]]
    mirror=lambda p:p+[(SCALE//2-a,b) for a,b in p[-2::-1]]
    return dict(x=x,left=mirror(l),right=mirror(r))


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('file',type=Path)
    ap.add_argument('--bins',type=int,default=16384)
    a=ap.parse_args()
    spec=json.loads(a.file.read_text()); blank,bad=certify(spec,a.bins)
    print(json.dumps(dict(blank=str(blank),bad=str(bad),p=float(bad),b=float(blank),bins=a.bins),indent=2))
