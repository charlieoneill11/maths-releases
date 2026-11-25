#!/usr/bin/env python3
"""Verify a six-coloring by interiors of simple polygons modulo a lattice.

Input JSON: {"period": [[ux,uy],[vx,vy]], "pieces": [{"color": 0,
"vertices": [[x,y], ...]}, ...]}. Give exact integers or strings such as
"1/3" and "0.125". Decimal JSON numbers are also parsed without rounding.
Colors are integer labels, at most six distinct. List each piece once, at any
lift. Boundaries have zero area and are left blank unless in a piece interior.
No geometry or numerical optimization libraries are needed.
"""
import argparse
import json
import math
from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import product
from pathlib import Path


def cross(a, b):
    return a[0]*b[1] - a[1]*b[0]


def dot(a, b):
    return a[0]*b[0] + a[1]*b[1]


def sub(a, b):
    return (a[0]-b[0], a[1]-b[1])


def edges(poly):
    return list(zip(poly, poly[1:]+poly[:1]))


def orient(a,b,c):
    return cross(sub(b,a),sub(c,a))


def segments_meet(a,b,c,d):
    if (max(a[0],b[0]) < min(c[0],d[0]) or max(c[0],d[0]) < min(a[0],b[0])
            or max(a[1],b[1]) < min(c[1],d[1]) or max(c[1],d[1]) < min(a[1],b[1])):
        return False
    return (orient(a,b,c)*orient(a,b,d)<=0 and orient(c,d,a)*orient(c,d,b)<=0)


def check_polygon(poly):
    n = len(poly)
    if n < 3 or len(set(poly)) != n:
        raise ValueError("Each polygon needs distinct cyclic vertices")
    sides = edges(poly)
    # Compare only edges with intersecting horizontal projections.
    ordered = sorted(enumerate(sides),key=lambda item:min(pt[0] for pt in item[1]))
    for h,(i,(a,b)) in enumerate(ordered):
        c = poly[(i+2)%n]
        if orient(a,b,c)==0 and dot(sub(a,b),sub(c,b))>0:
            raise ValueError("Backtracking adjacent edges")
        for k in range(h+1,n):
            j,(e,f) = ordered[k]
            if min(e[0],f[0])>max(a[0],b[0]):
                break
            if abs(i-j) not in (1,n-1) and segments_meet(a,b,e,f):
                raise ValueError("Self intersection")
    area2 = sum(cross(a,b) for a,b in sides)
    if not area2:
        raise ValueError("Degenerate polygon")
    if area2 < 0:
        poly.reverse()
    return abs(area2)


def convex_parts(poly):
    # Ear clipping supplies convex polygons for the overlap predicate. The
    # internal diagonals have zero area, so positive-area intersection of
    # two original polygon interiors forces two convex interiors to overlap.
    if all(orient(poly[i-2],poly[i-1],p)>=0 for i,p in enumerate(poly)):
        return [poly]
    # A strict kernel point gives a faster fan triangulation when available.
    lx,rx,ly,ry = bbox(poly)
    hub = ((lx+rx)//2,(ly+ry)//2)
    if all(orient(a,b,hub)>0 for a,b in edges(poly)):
        return [[hub,a,b] for a,b in edges(poly)]
    remainder = poly[:]
    triangles = []
    while len(remainder)>3:
        for i,b in enumerate(remainder):
            a,c = remainder[i-1],remainder[(i+1)%len(remainder)]
            turn = orient(a,b,c)
            if turn < 0:
                continue
            if turn:
                if any(orient(a,b,p)>=0 and orient(b,c,p)>=0 and orient(c,a,p)>=0
                       for p in remainder if p not in (a,b,c)):
                    continue
                triangles.append([a,b,c])
            remainder.pop(i)
            break
        else:
            raise ValueError("Unable to triangulate simple polygon")
    if orient(*remainder)>0:
        triangles.append(remainder)
    return triangles


def overlaps(p,q):
    # For full-dimensional closed convex polygons, their interiors intersect
    # precisely when all edge-normal projection intervals overlap strictly.
    # Since both are CCW, a supporting edge separates iff the other vertices
    # lie in its exterior closed halfplane.
    for first,second in ((p,q),(q,p)):
        for a,b in edges(first):
            edge = sub(b,a)
            if all(cross(edge,sub(v,a)) <= 0 for v in second):
                return False
    return True


def point_segment_at_least_unit(p,a,b,unit2):
    edge, rel = sub(b,a), sub(p,a)
    t_num, t_den = dot(rel,edge), dot(edge,edge)
    if t_num <= 0:
        return dot(rel,rel) >= unit2
    if t_num >= t_den:
        diff = sub(p,b)
        return dot(diff,diff) >= unit2
    return cross(edge,rel)**2 >= unit2*t_den


def distance_case(p,q,unit2,identical):
    # Every interior distance is strictly below the maximum on the closures
    # and every positive interior distance strictly above the minimum. The
    # product of interiors is connected, so these endpoint tests are exact.
    # Group consecutive edges for inexpensive exact box pruning. Group g
    # contains both its edge start vertices and the final edge's endpoint.
    def groups(poly):
        chunk = 16
        closed = poly+[poly[0]]
        for k in range(0,len(poly),chunk):
            arc = closed[k:k+chunk+1]
            yield arc,bbox(arc)

    pp,qq = list(groups(p)),list(groups(q))

    def near(a,b):
        arc,(lx,rx,ly,ry) = a
        brc,(ax,bx,ay,by) = b
        dx,dy = max(abs(lx-bx),abs(rx-ax)),max(abs(ly-by),abs(ry-ay))
        if dx*dx+dy*dy <= unit2:
            return True
        return all((x-u)**2+(y-v)**2<=unit2 for x,y in arc[:-1] for u,v in brc[:-1])

    if all(near(a,b) for a,b in product(pp,qq)):
        return "near"
    if identical:
        return None
    # Disjoint interiors imply a closest pair is attained at a vertex and an
    # edge (including tangencies and parallel or collinear edges).
    for a,(lx,rx,ly,ry) in pp:
        for b,(ax,bx,ay,by) in qq:
            dx,dy = max(0,lx-bx,ax-rx),max(0,ly-by,ay-ry)
            if dx*dx+dy*dy>=unit2:
                continue
            for first,second in ((a,b),(b,a)):
                if any(not point_segment_at_least_unit(v,c,d,unit2)
                       for v in first[:-1] for c,d in zip(second,second[1:])):
                    return None
    return "far"


def translated_overlap(first,second,x,y):
    for p,(lx,rx,ly,ry) in first:
        for q,(ax,bx,ay,by) in second:
            if bx+x<=lx or ax+x>=rx or by+y<=ly or ay+y>=ry:
                continue
            if overlaps(p,[(u+x,v+y) for u,v in q]):
                return True
    return False


def bbox(poly):
    x,y = zip(*poly)
    return (min(x),max(x),min(y),max(y))


def ceil_div(a,b):
    return -((-a)//b)


def shifts(pb,qb,u,v,det,pad):
    # T = m*u+n*v must put the two bounding boxes within pad in both axes.
    # Transform the resulting rectangle to lattice coordinates by Cramer's
    # rule. Its extrema are attained at corners, even for skew periods.
    lx,rx = pb[0]-qb[1]-pad,pb[1]-qb[0]+pad
    ly,ry = pb[2]-qb[3]-pad,pb[3]-qb[2]+pad
    corners = list(product((lx,rx),(ly,ry)))
    num_m = [cross(c,v) for c in corners]
    num_n = [cross(u,c) for c in corners]
    for m in range(ceil_div(min(num_m),det),max(num_m)//det+1):
        for n in range(ceil_div(min(num_n),det),max(num_n)//det+1):
            dx,dy = m*u[0]+n*v[0],m*u[1]+n*v[1]
            if lx <= dx <= rx and ly <= dy <= ry:
                yield m,n,dx,dy


def read_point(p):
    if not isinstance(p,list) or len(p)!=2:
        raise ValueError("Expected a Cartesian coordinate pair")
    if any(isinstance(c,(bool,float)) for c in p):
        raise ValueError("Supply coordinates exactly as integers, strings or decimals")
    return tuple(Fraction(c) for c in p)


def verify(spec):
    ru,rv = map(read_point,spec["period"])
    pcs = spec["pieces"]
    colors = [piece["color"] for piece in pcs]
    if any(type(c) is not int for c in colors) or len(set(colors))>6:
        raise ValueError("Use at most six integer color labels")
    raw = [[read_point(p) for p in piece["vertices"]] for piece in pcs]
    den = math.lcm(*(c.denominator for poly in [[ru,rv],*raw] for p in poly for c in p))

    def scale(p):
        return tuple(c.numerator*(den//c.denominator) for c in p)
    u,v = scale(ru),scale(rv)
    det = cross(u,v)
    if not det:
        raise ValueError("Singular period lattice")
    if det < 0:
        v = (-v[0],-v[1])
        det = -det
    polygons = [list(map(scale,poly)) for poly in raw]
    total_area2 = sum(check_polygon(poly) for poly in polygons)
    parts = [[(t,bbox(t)) for t in convex_parts(p)] for p in polygons]
    boxes = list(map(bbox,polygons))
    counts = dict(near=0,far=0,different=0)
    for i,p in enumerate(polygons):
        for j in range(i,len(polygons)):
            same = colors[i]==colors[j]
            for m,n,x,y in shifts(boxes[i],boxes[j],u,v,det,den if same else 0):
                if i==j and (m,n)<(0,0):
                    continue
                identical = i==j and m==n==0
                q = [(a+x,b+y) for a,b in polygons[j]]
                if not identical and translated_overlap(parts[i], parts[j], x, y):
                    raise ValueError(f"Interior overlap at pieces {i}, {j} shift {m,n}")
                if same:
                    case = distance_case(p,q,den**2,identical)
                    if case is None:
                        raise ValueError(f"Unit distance at pieces {i}, {j} shift {m,n}")
                    counts[case] += 1
                else:
                    counts["different"] += 1
    hole = 1 - Fraction(total_area2,2*det)
    if not 0<=hole<=1:
        raise ValueError("Impossible total area")
    with localcontext() as ctx:
        ctx.prec = 25
        approx = str(Decimal(hole.numerator)/Decimal(hole.denominator))
    return dict(pieces=len(pcs),colors=len(set(colors)),hole_fraction=str(hole),
                hole_decimal=approx,below_target=hole<Fraction(1,10000),
                checked_pairs=counts)


if __name__=="__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("pattern",type=Path)
    ns = ap.parse_args()
    print(json.dumps(verify(json.loads(ns.pattern.read_text(),parse_float=Decimal)),indent=2))
