"""Standalone finite-order certificate using a heptagon, a hole diamond, and forests."""
from fractions import Fraction as F
from pathlib import Path
import json
from finite_polygon_cert import calculate,spec_geometry
from hybrid_order import diamond_credits


def critical_edge_ceiling(N):
    # Apply the paired circle-crossing and common-neighbor bounds to a
    # 7-critical induced subgraph of size <= N, minimum degree >= 6.
    lo,hi=0,N*(N-1)//2+1
    while lo+1<hi:
        m=(lo+hi)//2
        if 4*m**3+58*N*m*m-29*N*N*m <=29*N**3*(N-1):lo=m
        else:hi=m
    return max(lo,(139*N)//20)


def report(path='finite_heptagon.json',N=10000):
    spec=json.loads(Path(path).read_text(),parse_float=F)
    x,y,z,tile=spec_geometry(spec)
    # Maximal intercepts of the cut-off right-angle corners. Verify both
    # supporting cuts directly; all quadrant copies of the diamond are blank.
    r=min(a for a,b in tile if b==0)
    l=min(b for a,b in tile if a==0)
    assert r>0 and l>0 and r<x-z and 2*l<y
    assert all(a/r+b/l>=1 and a/r+(y-b)/l>=1 for a,b in tile)
    geom=calculate(spec)
    blank=F(geom['blank']);p=F(geom['edge_probability_upper'])
    half=F(14,10000)
    C,B=diamond_credits(x,y,r,l,half)
    # Round the geometric credits strictly down to elementary constants.
    c=F(434,10**7); b=F(575,10**10)
    assert 0<b<=B and c<=C and b<p
    M=critical_edge_ceiling(N)
    def saving(s):
        # k+s(s-1) cross edges at most, and at most binom(s,2)
        # discarded-discarded edges. The k<=N relaxation simplifies the bound.
        return s*c+max(0,M-N-3*s*(s-1)//2)*b
    min_credit=min(saving(s) for s in range(N+1))
    upper=N*blank+M*p-min_credit
    assert upper<1
    return dict(order=N,critical_edge_ceiling=M,blank=str(blank),
                same_color_edge_upper=str(p),diamond_r=str(r),diamond_l=str(l),
                cone_half_angle=str(half),short_pair_credit=str(c),unit_edge_credit=str(b),
                forest_discount=str(min_credit),bad_event_upper=str(upper),
                bad_event_decimal=float(upper))


if __name__=='__main__':
    print(json.dumps(report(),indent=2))
