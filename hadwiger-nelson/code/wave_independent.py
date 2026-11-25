"""Independent angular enclosure for the symmetric wavy six-label finite bound.

All geometry uses integer upper bounds at the profile knots. This checker
uses monotonicity of the half-height left profile and its exact minimum over
each angular bin's vertical displacement range; no derivative margin is used.
"""
import argparse
from bisect import bisect_right
from fractions import Fraction as F
import json
from math import floor
from pathlib import Path

S=10**12
H=S//2


def ceil_div(a,b):
    return -((-a)//b)


def twice_overlap(dx,dl,dh,L,R,Rpos):
    """Integral upper bound for fixed dx_lower and |dy| anywhere in [dl,dh]."""
    if dx >= max(R.values()) or dl>=H:
        return 0
    # L is nonincreasing up to H/2 and nondecreasing after it. The minimum
    # of L(z-d) for d in [dl,dh] occurs at the allowed height nearest H/2.
    # Its profile is thus a translated L with the middle plateau extended.
    folded={h+dl:q for h,q in L.items() if h<=H//2}
    folded.update({h+dh:q for h,q in L.items() if h>=H//2})
    heights=sorted(folded)
    knots=sorted(set([dl,H]+[t for t in Rpos if dl<t<H]+[t for t in heights if dl<t<H]))
    def upward(profile,breaks,z,sign):
        i=bisect_right(breaks,z)-1
        a=breaks[i];p=sign*profile[a]
        if z==a:return p
        b=breaks[i+1];q=sign*profile[b]
        return p+ceil_div((q-p)*(z-a),b-a)
    widths=[upward(R,Rpos,z,1)+upward(folded,heights,z,-1)-dx for z in knots]
    twice=0
    for i in range(1,len(knots)):
        a,b=sorted(widths[i-1:i+1])
        if b<=0:continue
        h=knots[i]-knots[i-1]
        twice+=(a+b)*h if a>=0 else ceil_div(b*b*h,b-a)
    return twice


def check(data,bins,n=10000):
    x=data['x'];L=dict(data['left']);R=dict(data['right'])
    assert type(x)==int and 9*S//10<x<S
    for name,g in [('left',L),('right',R)]:
        assert len(g)==len(data[name]) and min(g)==0 and max(g)==H
        assert all(type(t)==type(v)==int and g[H-t]==v for t,v in g.items())
    assert all(0<=r<S//5 for r in L.values()) and all(4*S//5<r<S for r in R.values())
    assert {h:R[h] for h in R if h<=H//2}=={h-H//2:2*x-R[h] for h in R if h>=H//2}
    if H//2 not in L:
        a=max(h for h in L if h<H//2);b=min(h for h in L if h>H//2)
        assert L[a]==L[b];L[H//2]=L[a]
    halves=sorted(h for h in L if h<=H//2)
    assert all(L[a]>=L[b] for a,b in zip(halves,halves[1:]))
    # (W3): L vanishes on [y0,H/2] for some y0<H/4. As L is nonincreasing,
    # nonnegative and affine between knots, its first zero is a knot.
    zeros=[h for h in halves if L[h]==0]
    assert zeros and 4*zeros[0]<H, 'W3 needs the first zero of the left profile below H/4'
    allh=sorted(L)
    q=F(sum((b-a)*(L[a]+L[b]) for a,b in zip(allh,allh[1:])),2*x*H)
    Rpos=sorted(R)
    total=0
    for i in range(bins):
        n2=bins*bins
        a,b=n2+i*i,n2+(i+1)**2
        xlo=(n2-(i+1)**2)*S//b
        xhi=ceil_div((n2-i*i)*S,a)
        ylo=2*S*bins*i//a
        yhi=ceil_div(2*S*bins*(i+1),b)
        # Drift from the two different same-color lattice offsets.
        area=twice_overlap(xlo,ylo,yhi,L,R,Rpos)
        dl=max(0,3*S//4-yhi,ylo-3*S//4)
        dh=max(3*S//4-ylo,yhi-3*S//4)
        area+=twice_overlap(2*x-xhi,dl,dh,L,R,Rpos)
        total+=ceil_div(area*bins,a)
    p=F(2*total,x*H)/F(314159,100000)
    # Evaluate AP circle crossing bound directly for m=M+1, where each
    # circle contains >=6 points in the proposed 7-critical subgraph.
    M=374318
    assert n==10000 and 2*(M+1)>=F('13.9')*n
    def crossing_cost(m):
        return F(8*m**3,58*n*n)+F(2*m*m,n)-m
    assert crossing_cost(M+1)>n*(n-1)>=crossing_cost(M)
    expectation=n*q+M*p
    return dict(blank=str(q),conflict=str(p),expectation=str(expectation),
                decimal=float(expectation),below_one=expectation<1)


if __name__=='__main__':
    pp=argparse.ArgumentParser(description=__doc__)
    pp.add_argument('spec');pp.add_argument('--bins',type=int,default=131072)
    args=pp.parse_args()
    print(json.dumps(check(json.loads(Path(args.spec).read_text()),args.bins),indent=2))
