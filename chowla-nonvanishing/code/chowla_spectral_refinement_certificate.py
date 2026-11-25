"""Exact rational verification of the higher Legendre modes.
Uses the 160-grid gain already certified by chowla_grid160_certificate.py.
"""
from fractions import Fraction as Q
from functools import cache
from math import factorial, lcm

import chowla_grid160_certificate as base
import chowla_joint_certificate as spline
import chowla_quadratic_certificate as quadratic

GRID = 160
OLD_GAIN = Q(25278375, 10**10)

# The coefficients below multiply P16, P18, ...; the key is 160t.
# Width zero denotes a deterministic term added to the old witness.
ADDED = {
    0: [-29178, -49586, 38499, 143, 39925, -9921, 27126, -14745, 19252, -16741, 12735, -14251],
    5: [-870168, 89725, 33939, 97095],
    20: [-270416, 176980, -33503, 39115],
    40: [-21424, 55884, 8610, 50448],
    60: [45099, 2172, 32428, 41136],
    80: [39661, -4705, 24324, 18822],
    100: [16892, -1307, 8248, 5824],
    120: [78, 1409, -2550, 1369],
    140: [1127, 1531, 5319, 3412],
    155: [-2324, 148, 5272, 4760],
}

def integer_spline(test):
    denominators = []
    segments = []
    for knot, jets in test:
        scaled = [value / Q(GRID**degree) for degree, value in enumerate(jets)]
        den = lcm(*(value.denominator for value in scaled))
        denominators.append(den)
        assert GRID*knot == int(GRID*knot)
        segments.append((int(GRID*knot), [int(den*value) for value in scaled], den))
    common = lcm(*denominators)
    return [(knot, [v*(common//den) for v in values]) for knot, values, den in segments], common

def convolution(left, right):
    # Derivative jumps of a convolution of truncated powers.
    lseg, lden = left
    rseg, rden = right
    jumps = {}
    for lk, ljet in lseg:
        for rk, rjet in rseg:
            jet = jumps.setdefault(lk+rk, [0]*(len(ljet)+len(rjet)))
            for i, vi in enumerate(ljet):
                for j, vj in enumerate(rjet):
                    jet[i+j+1] += vi*vj
    @cache
    def integral_jets(n):
        fac = factorial(n+max(len(row)-1 for row in jumps.values()))
        rows = [(knot, [v*(fac//factorial(n+i)) for i,v in enumerate(row)])
                for knot,row in jumps.items()]
        return rows, lden*rden*fac*GRID**(n+1)
    @cache
    def primitive(n,x):
        y = x*GRID
        assert y == int(y)
        total = 0
        rows, den = integral_jets(n)
        for knot, row in rows:
            shift = int(y)-knot
            if shift > 0:
                poly = 0
                for coef in reversed(row):
                    poly = poly*shift+coef
                total += poly*shift**n
        return Q(total,den)
    return primitive

def row(tag,coefficients):
    t=Q(tag,GRID)
    return t,integer_spline(spline.legendre_test(coefficients,1-t)),sum(map(abs,coefficients))

def linear_inner(left,right):
    t,r,_=left
    u,s,_=right
    f=convolution(r,s)
    if t and u:
        return quadratic.cumulant(f,[t,u])+base.cov(t,u)*spline.mean(f)
    if t or u:
        return spline.covariance(f,t+u)
    return spline.mean(f)

def quadratic_inner(left,right):
    t,r,_=left
    a,b,p,_=right
    f=convolution(r,p)
    if not t:
        return quadratic.cumulant(f,[a,b])
    return (quadratic.cumulant(f,[t,a,b])+base.cov(t,a)*spline.covariance(f,b)
            +base.cov(t,b)*spline.covariance(f,a)+base.rect3(t,a,b)*spline.mean(f))

def central_bounds(H,linear_rows,quadratic_rows):
    center=Q(0)
    err=Q(0)
    for t,r,weight in linear_rows:
        if t:
            center+=spline.covariance(convolution(H,r),t)
            err+=8*t*t*(1-t)*weight
    for a,b,p,weight in quadratic_rows:
        center+=quadratic.cumulant(convolution(H,p),[a,b])
        err+=64*a*b*(1-a-b)*weight
    err*=Q(1,10**12)
    return center-err,center+err

def main():
    # Compare the integer implementation with the original rational spline
    # evaluator, including the higher degrees and evaluation at a knot.
    left=spline.legendre_test([0]*7+[1,0,-3],Q(7,8))
    right=spline.legendre_test([2,1],Q(3,4))
    original=spline.convolution(left,right)
    integer=convolution(integer_spline(left),integer_spline(right))
    for order in (0,1,3,5):
        for x in (Q(-1,2), Q(1,8), Q(7,10), Q(2)):
            assert original(order,x)==integer(order,x)
    H=integer_spline(spline.approximate_H())
    old=[row(0,[-c for c in base.projection])]
    old.extend(row(i,coefs) for i,coefs in enumerate(base.linear_rows,1))
    pairs=[]
    for (i,k), coefs in zip(base.pair_indices,base.quadratic_rows):
        a,b=Q(i,40),Q(k,40)
        p=integer_spline(spline.legendre_test(coefs,1-a-b))
        pairs.append((a,b,p,sum(map(abs,coefs))))
    new=[row(key,[0]*7+coefs) for key,coefs in ADDED.items()]
    old_lo,old_hi=central_bounds(H,old,pairs)
    add_lo,_=central_bounds(H,new,[])
    cross=sum(linear_inner(r,s) for r in new for s in old)
    cross+=sum(quadratic_inner(r,s) for r in new for s in pairs)
    norm=sum(linear_inner(r,s) for r in new for s in new)
    # D_old < C_old^2/(2*OLD_GAIN). Only the norm change is needed.
    D_hi=old_hi**2/(2*OLD_GAIN)+2*cross+norm
    C_lo=old_lo+add_lo
    assert old_lo>0 and C_lo>0 and D_hi>0
    gain=C_lo*C_lo/(2*D_hi)
    density=(19-Q(3916317365,10**9))/16+gain
    print("Certified gain and nonvanishing proportion:",float(gain),float(density))
    assert gain>Q(25316736862,10**13)
    assert density>Q(9452618383,10**10)

if __name__=='__main__':
    main()
