"""Certify a sup-norm vertex comparison with an inscribed ideal-tile mesh.

If a translated rational input tile contains a test rectangle padded by
vertices + abs(m)*period_x in each direction, its ideal counterpart at
period index (m,n) contains the unpadded rectangle. No padding is needed
for common global translations of the entire argument.
"""
import json
import sys
from fractions import Fraction as F
from ideal_area import Interval as I, D
from ideal_distance import OPPOSITE, add, dot, ideal_vertices, mul, sub


def check(spec):
    x,y,w,a=ideal_vertices()
    uv,vel=spec['period']
    ux,uy=map(F,uv)
    assert uy==F(3,4) and tuple(map(F,vel))==(0,F(3,2))
    raw=spec['pieces']
    assert [p['color'] for p in raw]==[1,3,2,4,6,5]
    n,rem=divmod(len(raw[0]['vertices'])-len(a),len(OPPOSITE))
    assert rem==0 and n>=0
    subdiv=n+1
    tile=[]
    for i,pt in enumerate(a):
        tile.append(pt)
        if i not in OPPOSITE:continue
        center=mul(add(pt,a[OPPOSITE[i]]),I.num('.5'))
        for j in range(1,subdiv):
            alpha=I.num(F(j,subdiv))
            z=sub(add(mul(pt,1-alpha),mul(a[i+1],alpha)),center)
            tile.append(add(center,mul(z,I.num('.5')/dot(z,z).sqrt())))
    # Compare displayed vertices only after computing all of their
    # enclosures independently. Coordinates of an interior point of a
    # segment are affine in its two vertices, with nonnegative weights.
    margin=F(0)
    for k,p in enumerate(raw):
        assert len(p['vertices'])==len(tile)
        for ref,(vx,vy) in zip(p['vertices'],tile):
            adjusted=(vx if k<3 else -vx,vy+(k%3)*y)
            for t,h in zip(map(F,ref),adjusted):
                margin=max(margin,abs(t-F(h.lo,D)),abs(t-F(h.hi,D)))
    lo,hi=F(x.lo,D),F(x.hi,D)
    period_error=max(abs(2*lo-ux),abs(2*hi-ux))
    return dict(vertices=margin,period_x=period_error,x_lo=lo,x_hi=hi)


if __name__=='__main__':
    with open(sys.argv[1]) as f: result=check(json.load(f))
    for key,value in result.items():
        print(key, value, 'approximately',float(value))
