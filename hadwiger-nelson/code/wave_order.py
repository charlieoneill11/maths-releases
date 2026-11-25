"""Certified orders for two stored wavy labelings, with and without forest credits.

A straight union bound uses the independently checked defect probabilities and
the sharpened edge ceiling for a vertex-minimal counterexample. The optional
forest bound uses only the separated-representative stars and vertical paths.
"""
import argparse
from fractions import Fraction as F
from itertools import combinations
from math import ceil, isqrt
from pathlib import Path
import hashlib
import json
from wave_independent import check, S, H
from wave_certificate import certify
from finite_10000 import critical_edge_ceiling
from hybrid_order import diamond_credits, cross_upper


def last_order(bound):
    low, high = 1, 20000
    assert bound(low) < 1 <= bound(high)
    while high-low > 1:
        mid = (low+high)//2
        if bound(mid) < 1:
            low = mid
        else:
            high = mid
    at, after = bound(low), bound(high)
    assert at < 1 <= after
    return dict(order=low, edges=critical_edge_ceiling(low), upper=str(at),
                upper_decimal=float(at), next_edges=critical_edge_ceiling(high),
                next_upper=str(after), next_decimal=float(after))


def diamond(spec):
    # Inscribe r-m*t <= L(t) at every left-profile knot on the lower half.
    # Between knots the inequality follows by affine interpolation. The
    # remaining quadrants follow from symmetry. Try positive pair slopes.
    points = [(F(a,S),F(b,S)) for a,b in spec['left'] if a<=H//2]
    best = (0,0,0)
    for (a,b),(c,d) in combinations(points,2):
        if b<=d:continue
        slope=(b-d)/(c-a)
        r=min(v+slope*t for t,v in points)
        l=r/slope
        if 0<l<F(1,4) and r*l>best[0]:
            best=(r*l,r,l)
    _,r,l = best
    assert r>0 and l>0 and all(v>=r*(1-t/l) for t,v in points)
    assert r < F(spec['x'],S)/4
    return r,l


def star_path_upper(n,q,p,angle,near,aligned):
    M=critical_edge_ceiling(n)
    assert p>=aligned and q>0
    separation=2*angle
    L=ceil(F(44,7)/separation)-1
    min_credit=None
    for s in range(n+1):
        if min_credit is not None and s*near>=min_credit:
            break
        k=n-s
        cross=cross_upper(k,s,L)
        inside=min(s*(s-1)//2,(s+isqrt(s*s*max(0,8*s-7)))//4)
        credit=s*near+max(0,M-cross-inside)*aligned
        if min_credit is None or credit<min_credit:
            min_credit=credit
    return n*q+M*p-min_credit


def forest_result(spec,q,p):
    r,l=diamond(spec)
    best=None
    for tick in range(24,35):
        a=F(tick,10000)
        C,B=diamond_credits(F(spec['x'],S),F(1,2),r,l,a)
        # Use the same downward-rounded credits for every graph size tested.
        C=(C*10**14//1)/F(10**14);B=(B*10**14//1)/F(10**14)
        result=last_order(lambda n:star_path_upper(n,q,p,a,C,B))
        if best is None or (result['order'],-F(result['upper']))>(best['order'],-F(best['upper'])):
            best=dict(**result,diamond_r=str(r),diamond_l=str(l),half_angle=str(a),
                      close_credit=str(C),unit_credit=str(B))
    return best


def evaluate(path,bins,forest=True):
    spec=json.loads(path.read_text())
    first=check(spec,bins)
    q,p_ind=map(F,(first['blank'],first['conflict']))
    q_other,p_other=certify(spec,bins)
    assert q_other==q
    return summarize(path,bins,spec,q,p_ind,p_other,forest)


def summarize(path,bins,spec,q,p_ind,p_other,forest=True):
    # Retain the larger bound as the common certificate. Both independently
    # derived enclosures therefore entail the reported integer.
    p=max(p_ind,p_other)
    direct=lambda value:last_order(lambda n:n*q+critical_edge_ceiling(n)*value)
    report=dict(file=path.name, sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                bins=bins,blank=str(q),independent_probability=str(p_ind),
                profile_probability=str(p_other),common_probability=str(p),
                independent_union=direct(p_ind),profile_union=direct(p_other),
                jointly_certified_union=direct(p))
    if forest:
        report['jointly_certified_forest']=forest_result(spec,q,p)
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bins',type=int,default=4194304)
    parser.add_argument('--no-forest',action='store_true')
    parser.add_argument('profiles',nargs='*',default=['wavy_short.json','wavy_optimized.json'])
    args=parser.parse_args()
    print(json.dumps([evaluate(Path(p),args.bins,not args.no_forest) for p in args.profiles],indent=2))
