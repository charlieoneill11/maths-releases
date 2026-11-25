"""Rigorous blank fraction and monochromatic unit-edge probability for a convex tile.

JSON input: {"x":"...","y":"...","z":"...","vertices":[["x0","y0"],...]}.
Each right-facing tile lies in its pentagonal master cell. Reflect to obtain
the left-facing tiles and repeat with Parts's six-color period lattice.
All geometric decisions and the reported probability bound are rational.
"""
import argparse
from bisect import bisect_left
from fractions import Fraction as F
from itertools import product
from math import ceil, floor
from pathlib import Path
import json
from verify import check_polygon, read_point, cross, sub


def clip(poly, edge, offset):
    """Intersect polygon with cross(edge,point) >= offset."""
    if not poly:
        return []
    out=[]
    p=poly[-1]; a=cross(edge,p)-offset
    for q in poly:
        b=cross(edge,q)-offset
        if (a<0)!=(b<0):
            t=a/(a-b)
            out.append((p[0]+t*(q[0]-p[0]),p[1]+t*(q[1]-p[1])))
        if b>=0:out.append(q)
        p=q; a=b
    return out


def area2(poly):
    return sum(cross(p,q) for p,q in zip(poly,poly[1:]+poly[:1]))


def spec_geometry(spec):
    x,y,z=map(F,[spec['x'],spec['y'],spec['z']])
    assert x>0 and y>0 and 0<=z<x
    poly=list(map(read_point,spec['vertices']))
    check_polygon(poly)
    master=[(F(0),F(0)),(x-z,F(0)),(x+z,y/2),(x-z,y),(F(0),y)]
    for a,b in zip(master,master[1:]+master[:1]):
        assert all(cross(sub(b,a),sub(p,a))>=0 for p in poly)
    for a,b in zip(poly,poly[1:]+poly[:1]):
        assert all(cross(sub(b,a),sub(p,a))>=0 for p in poly),"Tile must be convex"
    while len(poly)>3:
        indices=[i for i,p in enumerate(poly) if cross(sub(p,poly[i-1]),sub(poly[(i+1)%len(poly)],p))==0]
        if not indices:break
        poly.pop(indices[0])
    assert set(poly)=={(a,y-b) for a,b in poly},"Tile needs mirror symmetry about half-height."
    return x,y,z,poly


def calculate(spec,bins=128,depth_limit=13):
    x,y,z,P=spec_geometry(spec)
    source_area=area2(P)/2
    ex=[p[0] for p in P]; ey=[p[1] for p in P]
    w,h=max(ex)-min(ex),max(ey)-min(ey)
    shifts=[]
    for i in range(ceil((-w-1)/(2*x)),floor(w/(2*x))+1):
        sy=3*i*y/2
        for j in range(ceil((-h-1-sy)/(3*y)),floor((h-sy)/(3*y))+1):
            shifts.append((2*i*x,sy+3*j*y))
    # For each side, event levels detect a vertex on an opposed supporting
    # line. The difference-body projection radius is a cheap exclusion test.
    edges=[]
    for a,b in zip(P,P[1:]+P[:1]):
        v=sub(b,a)
        proj=[cross(v,p) for p in P]
        base=cross(v,a)
        levels=sorted({sgn*(s-base) for s in proj for sgn in (-1,1)})
        edges.append((v,base,levels,max(proj)-min(proj)))
    def intersection2(dx,dy):
        q=P
        for v,base,_,_ in edges:
            q=clip(q,v,base+cross(v,(dx,dy)))
            if not q:return F(0)
        return area2(q)
    def uv(t):
        return (1-t*t)/(1+t*t),2*t/(1+t*t)
    # Absolute outward rounding per angular interval, avoiding denominator
    # growth across thousands of exact clipped-polygon area calculations.
    grid=10**25
    counts={'stable':0,'fallback':0}
    def integrate(t0,t1,sx,sy,depth):
        xmax,ymin=uv(t0); xmin,ymax=uv(t1)
        if xmin+sx>=w or xmax+sx<=-w or ymin+sy>=h or ymax+sy<=-h:
            return 0
        stable=True
        relax=[]
        for v,base,levels,radius in edges:
            lo=v[0]*(sy+(ymin if v[0]>=0 else ymax))-v[1]*(sx+(xmax if v[1]>=0 else xmin))
            hi=v[0]*(sy+(ymax if v[0]>=0 else ymin))-v[1]*(sx+(xmin if v[1]>=0 else xmax))
            if lo>=radius or hi<=-radius:return 0
            hit=bisect_left(levels,lo)
            if hit<len(levels) and levels[hit]<=hi:stable=False
            relax.append((v,base+lo))
        if stable:
            counts['stable']+=1
            # Area times (1+t²)² is quartic within this arrangement cell.
            # Taylor's upper bound on (1+h)^(-3) below yields a degree-eight
            # polynomial, integrated exactly by the nine-node Newton-Cotes rule.
            weighted=F(0)
            for k,weight in enumerate((989,5888,-928,10496,-4540,10496,-928,5888,989)):
                t=t0+(t1-t0)*F(k,8); dx,dy=uv(t)
                hrel=(t*t-t0*t0)/(1+t0*t0)
                A2=intersection2(dx+sx,dy+sy)
                assert A2>=0
                weighted+=weight*A2*(1+t*t)**2*(1-3*hrel+6*hrel*hrel)
            upper=(t1-t0)*weighted/(28350*(1+t0*t0)**3)
        elif depth<depth_limit:
            mid=(t0+t1)/2
            return integrate(t0,mid,sx,sy,depth+1)+integrate(mid,t1,sx,sy,depth+1)
        else:
            counts['fallback']+=1
            q=P
            for edge,offset in relax:
                q=clip(q,edge,offset)
                if not q:return 0
            upper=(t1-t0)*area2(q)/(1+t0*t0)
        assert upper>=0
        return ceil(upper*grid)
    total=sum(integrate(F(j,bins),F(j+1,bins),sx,sy,0)
              for j in range(bins) for sx,sy in shifts)
    # Four quadrants have equal integrals. The average over the six labels
    # reduces to normalization by one master-cell area because reflections
    # preserve the isotropic unit-edge distribution.
    prob=F(total,grid)*2/(F('3.14159265358979')*x*y)
    blank=1-source_area/(x*y)
    assert 0<=blank<=1
    return {'blank':str(blank),'edge_probability_upper':str(prob),
            'blank_decimal':float(blank),'edge_decimal':float(prob),'bins':bins,
            'depth':depth_limit,'shifts':len(shifts),'interval_counts':counts}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('spec',type=Path)
    parser.add_argument('--bins',type=int,default=128)
    parser.add_argument('--depth',type=int,default=13)
    parser.add_argument('--n',type=int)
    parser.add_argument('--m',type=int)
    args=parser.parse_args()
    spec=json.loads(args.spec.read_text(),parse_float=F)
    results=calculate(spec,args.bins,args.depth)
    if args.n is not None:
        assert args.m is not None
        bound=args.n*F(results['blank'])+args.m*F(results['edge_probability_upper'])
        results.update(expected_upper=str(bound),expected_decimal=float(bound),certified=bound<1)
    print(json.dumps(results,indent=2))
