"""Twelve-mode upper shoulder budget on the final 11/5 splice.

Integer rotations construct a rigorously enclosed mesh. A stack decomposes
the resulting majorant into weighted counts over contiguous level intervals.
"""
from fractions import Fraction as Q
from math import isqrt
from check_bounded_factors import lowlog, highlog
from check_cutoffs import tenth_root
from check_three_mode import PI_HI, cos_pi
from check_twelve_modes import W
from check_farey_sieve import farey_improvement

FIRST = 32_800_000_000_000
LAST = 33_116_944_888_557
GRID = 65536
T = 10**22
HEIGHT = T*10**6
U = Q('1.000000000001')


def round_cos(q):
    lo,hi=cos_pi(q)
    v=(T*lo).__floor__()
    assert hi-Q(v,T)<Q('3e-18')
    return v


def level_intervals(weights=W):
    # A rotation step has Euclidean error <5e-18; the two floors cost <2/T.
    # Its true coefficient has modulus 1. Induction bounds all component
    # errors by 6e-18*(GRID+1)*(1+5e-18)**GRID < 1e-12.
    assert 2*Q('6e-18')*(GRID+1)<Q('1e-12') and GRID*Q('5e-18')<Q(1,2)
    assert sum(abs(w) for w in weights)<10**6
    curvature=sum(abs(w)*(PI_HI*(2*j+1)/4)**2 for j,w in enumerate(weights))/10**6
    assert curvature<16
    nodes=[0]*(GRID+1)
    for j,w in enumerate(weights):
        k=2*j+1
        arg=Q(k,4)
        x,y=round_cos(arg),round_cos(Q(1,2)-arg)
        step=Q(k,4*GRID)
        c,s=round_cos(step),round_cos(Q(1,2)-step)
        for i in range(GRID+1):
            nodes[i]+=w*x
            x,y=(c*x-s*y)//T,(s*x+c*y)//T
    padding=(HEIGHT*(Q('1e-12')+Q(2,GRID**2))).__ceil__()
    cells=[max(0,max(x,y)+padding) for x,y in zip(nodes,nodes[1:])]
    stop=(Q('.28')*GRID).__ceil__()
    assert all(cells[i]>=cells[i+1] for i in range(stop))
    assert cells[stop]==0
    # horizontal layer cake: a popped stack entry is a complete component
    # over the levels (max(current,parent_height), old_height].
    stack=[(0,0)]
    strips={}
    for right,h in enumerate(cells+[0]):
        left=right
        while stack[-1][0]>h:
            old,left=stack.pop()
            drop=old-max(h,stack[-1][0])
            width=right-left
            strips[width]=strips.get(width,0)+drop
        if h>stack[-1][0]:
            stack.append((h,left))
    assert sum(w*h for w,h in strips.items())==sum(cells)
    assert Q(sum(strips.values()),HEIGHT)<Q('.14')
    return strips


def sieve_constants():
    # H_n−log n−1/(2n)<Euler's constant by the trapezoidal bound.
    m=500
    eta=sum(Q(1,k) for k in range(1,m+1))-highlog(m)-Q(1,2*m)
    for p in range(2,20_001):
        if all(p%k for k in range(2,isqrt(p)+1)):
            eta+=lowlog(p)/(p*(p-1))
    assert eta>Q('1.33252')
    # Previous Farey verifier's rectangle integrals are fixed; only the
    # error from the summatory function is divided by sqrt(z).
    g1,g2=farey_improvement(1000),farey_improvement(2000)
    intercept=2*g2-g1
    error=2000*(g2-g1)
    assert intercept>Q('.13723') and error<Q('3.151')


def budget(strips, first=FIRST, last=LAST):
    sqrt_a=first*tenth_root(first)[0]
    p=Q('1.1')*tenth_root(first)[0]*first/(first+1)
    pmax=Q('1.1')*tenth_root(last+1)[1]*(last+1)/last
    smallL=Q('1.1')*lowlog(first)
    largeL=Q('1.1')*highlog(last+1)
    assert 2*Q('1.1')/first < (U-1)/U
    assert pmax*(last+1)*tenth_root(last+1)[1]*U<3*10**16
    # Absolute +1 in each interval count, both shoulders included.
    assert 2*Q('.14')*2*largeL*U**2/sqrt_a<Q('1e-9')
    fee=2*(1+PI_HI/4)*Q('2.44')
    scale=10**21
    accum=0
    den_min=Q(10);den_max=Q(0)
    for w,h in strips.items():
        v=Q(w,GRID)
        length=p*sqrt_a*v/U
        assert length>10**10
        N=length.__floor__()-1
        z=isqrt(3*N//4)
        zz=isqrt(z)
        c=(2*Q('1.33252')*z/(z+1)-highlog(Q(16,3))-fee/zz)
        if z>=470001:
            c+=Q('.13723')-Q('3.151')/zz
        else:
            # The H0 floor is valid as well; use whichever bound is stronger.
            c=max(c,Q('.8601'))
        den_min=min(den_min,c);den_max=max(den_max,c)
        bias=lowlog(p*v)+c-highlog(U)
        l=largeL if bias>=0 else smallL
        # theta=log(y)/sqrt(y) relative to 2L/exp(L) is at most U^2:
        # its displacement obeys |log(y/a)|≤2D.
        contribution=8*Q(h,HEIGHT)*l*v/(l+bias)*U**3
        accum+=(scale*contribution).__ceil__()
    charge=Q(accum,scale)
    print('Sieve constants over all widths:',float(den_min),float(den_max),flush=True)
    print('Certified shoulder charge including all distortions:',float(charge),flush=True)
    return charge


if __name__=='__main__':
    sieve_constants()
    strips=level_intervals()
    bound=budget(strips)
    assert bound<Q('.09493266384')
    from check_twelve_modes import F
    main=Q('1.00000063406447')
    assert F(Q(0))[0]>main
    k=main-Q('.09493266384')+Q('.00036975')
    norm=Q('.76582484235')
    c=Q('1.37996409425')
    # Residual allowances in the explicit formula at this particular splice.
    d=Q('1.1')/FIRST
    sqrt_a=FIRST*tenth_root(FIRST)[0]
    top=(LAST+1)*tenth_root(LAST+1)[1]
    sigu=Q('1.1')*(LAST+1)*tenth_root(LAST+1)[1]/LAST
    assert sqrt_a>7*10**14 and sigu<26 and 2*highlog(top)+1<71
    assert (2*highlog(top)+1)/lowlog(2)<103
    assert 1+2*sigu*U < 54
    higher=103*54*71*U/sqrt_a
    endpoints=2*71*U/sqrt_a
    dmin=Q('1.1')/(LAST+1)
    counts=2*d*((3+Q('.15')*highlog(7/dmin))*625+300)+10*d
    assert counts+higher+endpoints+Q('1e-9')+Q('1e-12') < Q('1e-8')
    def interval(n,k):
        a,b=tenth_root(n)
        m=k*Q(11*n,10*(n+1))
        return (m*a-norm*highlog(Q(10*(n+1),11))+c,
                m*b-norm*lowlog(Q(10*(n+1),11))+c)
    def first_passing(l,r,kbase):
        assert interval(l,kbase)[1]<0<interval(r,kbase)[0]
        while r-l>1:
            u=(l+r)//2
            lo,hi=interval(u,kbase)
            if lo>0:
                r=u
            else:
                assert hi<0
                l=u
        print('Coefficient',kbase,'first integer certified',r,'margin',float(interval(r,kbase)[0]),flush=True)
        return r
    assert first_passing(FIRST,LAST,k)==32_838_533_823_725
    l,r=32_830_000_000_000,32_840_000_000_000
    assert Q('1.1')*k*Q('.1')*tenth_root(l)[0]*l/(l+1) > norm
    narrow=budget(strips,l,r)
    from check_local_histogram import splice_gain,shoulder_layers,read_histogram
    actual_gain=splice_gain(l,r,shoulder_layers(),read_histogram())
    narrow=(narrow*10**11).__ceil__()*Q(1,10**11)
    gain=(actual_gain*10**11).__floor__()*Q(1,10**11)
    print('Narrow shoulder upper and histogram lower:',float(narrow),float(gain),flush=True)
    assert first_passing(l,r,main-narrow+gain)==32_836_026_647_689
