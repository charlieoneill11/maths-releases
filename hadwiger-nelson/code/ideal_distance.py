"""Verify all ideal same-color distance constraints by intervals and circle identities.

Requires ideal_area.py. The interval geometry is for the closure root there.
Floating point is used solely to suggest directions for strict separation.
"""
from itertools import combinations, product
from math import hypot
from ideal_area import Interval as I, D, arcsin, compute


def add(a,b):
    return tuple(x+y for x,y in zip(a,b))


def sub(a,b):
    return tuple(x-y for x,y in zip(a,b))


def mul(a,c):
    return tuple(x*c for x in a)


def dot(a,b):
    return sum((x*y for x,y in zip(a,b)),I.num(0))


def ideal_vertices():
    n=I.num('.0033448254428846693594959344084790204661219925262831')
    low=I.num('.00999872202647143777010571984520501496174154458')
    high=low+I.num('1e-47')
    assert compute(n,low)[0].lo>0>compute(n,high)[0].hi
    m=I(low.lo,high.hi)
    return vertices_from_parameters(n,m)


def vertices_from_parameters(n,m):
    """Build the rectangle geometry on a proven root of its closure equation."""
    y=I.num('.5')
    l=m+n
    leg=lambda t:(1-t*t).sqrt()
    uy=(3*y/2+l)/2
    ux=leg(uy)
    p=(leg(y/2-l)-leg(y/2+n-m))/2
    q=p+(m-n)*uy/ux
    x=ux-(p+q)/2
    d=(leg(y-2*n)-leg(y))/2
    r=q+d
    z=(x-leg(y)-q-2*d)/(1-4*n/y)
    s=d-4*n*z/y
    t=4*n*z/y-p
    zero=I.num(0); h=I.num('.04')
    # Exact symmetric joins on the midline, slope +/- uy/ux.
    b=[(zero,l),(p,m),(q,n),(r,zero),(x-z-s,zero),(x-z+4*n*z/y,n),
       (x-uy/ux*h,y/4-h),(x+uy/ux*h,y/4+h),(x+z-4*n*z/y,y/2-n),
       (x+z-t,y/2)]
    b += [(a,y-c) for a,c in reversed(b[:-1])]
    return x,y,(ux,uy),b


OPPOSITE={0:9,9:0,2:13,13:2,4:15,15:4,8:17,17:8}


def model(vertices=None):
    x,y,w,a=ideal_vertices() if vertices is None else vertices
    hulls=[]; disk_vertices={}
    for i,p in enumerate(a):
        j=(i+1)%len(a); q=a[j]
        h=[(p,i),(q,j)]
        if i in OPPOSITE:
            k=OPPOSITE[i]
            # Matching corners on the opposite chord are antipodal. The
            # rectangle identities in refine_parts.py give this equal center
            # for both endpoint pairs and radius 1/2 by their unit diagonals.
            o=mul(add(p,a[k]),I.num('.5'))
            s=sub(mul(add(p,q),I.num('.5')),o)
            # The tangents at p and q intersect at o+s/(4|s|^2).
            # Their triangle with p,q contains the whole minor arc.
            v=add(o,mul(s,1/(4*dot(s,s))))
            h.append((v,None))
            disk_vertices[i]={i,j,k,k+1}
        hulls.append(h)
    return x,y,w,a,hulls,disk_vertices


def diameter(hulls, disks):
    antipodes={tuple(sorted((k+h,t+h))) for k,t in OPPOSITE.items() for h in (0,1)}
    def below(i,j):
        for v,label in hulls[j]:
            if label in disks.get(i,set()):
                continue
            if any(dot(sub(p,v),sub(p,v)).hi>D for p,l in hulls[i]
                   if l is None or label is None or tuple(sorted((l,label))) not in antipodes):
                return False
        return True
    for i,j in product(range(len(hulls)),repeat=2):
        if OPPOSITE.get(i)==j: # Actual arcs lie on a single half-radius circle.
            continue
        if below(i,j) or below(j,i):
            continue
        # Straight edges may meet the antipodal endpoints of two arc pairs.
        antipodes={tuple(sorted((k+h,t+h))) for k,t in OPPOSITE.items() for h in (0,1)}
        for p,s in hulls[i]:
            for v,t in hulls[j]:
                if s is not None and t is not None and tuple(sorted((s,t))) in antipodes:
                    continue
                assert dot(sub(p,v),sub(p,v)).hi<=D,(i,j,s,t)


def mean(p):
    return tuple((t.lo+t.hi)/(2*D) for t in p)


def trial_directions(vertices,others):
    for sign,first,second in [(1,vertices,others),(-1,others,vertices)]:
        for a in first:
            for b,c in combinations(second,2):
                dx,dy=c[0]-b[0],c[1]-b[1]
                s=max(0,min(1,((a[0]-b[0])*dx+(a[1]-b[1])*dy)/(dx*dx+dy*dy)))
                yield (sign*(b[0]+s*dx-a[0]),sign*(b[1]+s*dy-a[1]))


def separated(first,second):
    # For triangles/segments try a separating line normal to a nearest pair.
    # Regardless of how it was found, all its projections are checked exactly.
    for raw in trial_directions([mean(p) for p,_ in first],[mean(p) for p,_ in second]):
        if hypot(*raw)<1e-7:continue
        axis=tuple(I.num(str(v)) for v in raw)
        low=min(dot(p,axis).lo for p,_ in second)
        high=max(dot(p,axis).hi for p,_ in first)
        if low>high and (low-high)**2>D*dot(axis,axis).hi:
            return True
    return False


def embedding(x,y,a,hulls):
    # Enclose the tile in a master region 0 < X < b(Y), 0 < Y < y.
    # b linearly interpolates the knots below. The identity
    # b(Y+y/2 mod y)=2*x-b(Y) holds at paired knots by construction,
    # hence on every segment. Reflection in the next column's vertical
    # wall consequently partitions the strips exactly.
    n=a[5][1]
    z=(x-a[5][0])/(1-4*n/y)
    b0=(x-z,I.num(0))
    bc=(x+z,y/2)
    knots=[b0,*a[5:9],bc,*a[10:14],(b0[0],y)]
    assert all(t[0].lo> I.num('.8').hi for t in knots)
    assert all(t[1].hi<v[1].lo for t,v in zip(knots,knots[1:]))
    # Left boundary stays in a narrow strip. Both actual boundaries
    # are graphs over height: each tangent intersection of an arc has
    # intermediate height, so both end tangents point monotonically in
    # height and have the same height sign over the shorter arc.
    for i in OPPOSITE:
        top=sorted([a[i][1],a[i+1][1]],key=lambda k:k.lo)
        assert top[0].hi<hulls[i][2][0][1].lo<=hulls[i][2][0][1].hi<top[1].lo
    for i in (0,1,2,15,16,17,18):
        assert all(p[0].hi<I.num('.1').lo for p,_ in hulls[i])
    for i in range(4,14):
        assert all(p[0].lo>I.num('.8').hi for p,_ in hulls[i])
    # The six straight wavy-side segments coincide with knot edges. The
    # other four segments here are arcs. Their shared tips are knots
    # and the remaining tangent-triangle vertices lie strictly to the
    # left of the relevant line, so the entire arc fits the master.
    for i,segment,coincident in [(4,0,5),(8,4,8),(9,5,10),(13,9,13)]:
        p,q=knots[segment:segment+2]
        for c,label in hulls[i]:
            if label==coincident:
                continue
            assert ((q[1]-p[1])*(c[0]-p[0])-(q[0]-p[0])*(c[1]-p[1])).hi<0
    assert a[4][0].hi<b0[0].lo
    # Horizontal tile edges lie at heights 0 and y, wholly in the master.
    print('Tile is simple and contained within the complementary master tiles.')


def area(x,y,a):
    def cross(v,w):
        return v[0]*w[1]-v[1]*w[0]
    shoelace=sum((cross(p,q) for p,q in zip(a,a[1:]+a[:1])),I.num(0))/2
    for i,k in OPPOSITE.items():
        p,q=a[i:i+2]
        c=mul(add(p,a[k]),I.num('.5'))
        assert cross(sub(q,p),sub(c,p)).lo>0
        d=sub(p,q)
        h=dot(d,d).sqrt()
        # Positive circular segment of radius one half and chord length h.
        shoelace+=(arcsin(h)-h*(1-h*h).sqrt())/4
    epsilon=1-shoelace/(x*y)
    lower=I.num('.0001430172087302812335283335209281857464')
    upper=I.num('.0001430172087302812335283335209281857465')
    assert lower.hi<epsilon.lo<=epsilon.hi<upper.lo
    print('Shoelace and circular segments confirm 0.0001430172087302812335283335209281857464 < epsilon')
    print('                               and epsilon < 0.0001430172087302812335283335209281857465')


def check(vertices=None):
    x,y,w,a,hulls,disks=model(vertices)
    diameter(hulls,disks)
    embedding(x,y,a,hulls)
    area(x,y,a)
    # Enclosures stay inside [0,1] x [0,1/2]. The same-color period lattice
    # is generated by (2x,3y/2),(0,3y). All nonzero shifts except (±2x,±3y/2)
    # consequently have an axis gap >=1, or have horizontal offset >=4x>2.
    for h in hulls:
        for (px,py),_ in h:
            assert 0<=px.lo<=px.hi<=D
            assert 0<=py.lo<=py.hi<=D//2
    assert (4*x).lo>2*D
    # Reflection in the tile's horizontal midline relates the remaining two
    # row offsets. Negating an offset preserves the distance between copies.
    offset=(2*x,3*y/2)
    plane=dot((x,3*y/4),w)
    wc=0;sc=0
    for h,k in product(hulls,repeat=2):
        k=[(add(p,offset),label) for p,label in k]
        # Labels 11,12 lie exactly on the wave midline. Translated labels
        # 1,2 project exactly one unit beyond it by perpendicularity and |w|=1.
        if (all(l in (11,12) or dot(p,w).hi<=plane.lo for p,l in h)
            and all(l in (1,2) or dot(p,w).lo>=plane.hi+D for p,l in k)):
            wc+=1
            continue
        assert separated(h,k),([s for _,s in h],[s for _,s in k])
        sc+=1
    print('Ideal tile diameter <= 1. Skew-shift closed boundary distance >= 1.')
    print('Wave-normal separation certificates:',wc,'other strict separators:',sc)


if __name__=='__main__':
    check()
