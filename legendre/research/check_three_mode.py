"""Rational enclosures for the three-mode prime-gap kernel and finite zero band."""

from functools import cache
from fractions import Fraction as Q

from check_cutoffs import log_bounds, tenth_root

K = Q(7, 5)
PI_LO = Q(3141592653589793238462643383279502884, 10**36)
PI_HI = PI_LO + Q(1, 10**36)
GRID = 2000
UNIT = 10**18


def check_pi():
    # Machin's formula with alternating-series remainder bounds.
    def arctan_bounds(t):
        total = Q(0)
        for j in range(36):
            total += (-1)**j*t**(2*j+1)/(2*j+1)
        return total, total+t**73/73
    lo5, hi5 = arctan_bounds(Q(1,5))
    lo239, hi239 = arctan_bounds(Q(1,239))
    assert PI_LO < 16*lo5-4*hi239 <= 16*hi5-4*lo239 < PI_HI


def discretize(lo, hi):
    return Q((lo * UNIT).__floor__(), UNIT), Q((hi * UNIT).__ceil__(), UNIT)


@cache
def cosine_first_quadrant(q):
    # q between 0 and 1/2. Taylor partial sums through degrees 22 and 24.
    def cosine_sum(t, count):
        term = total = Q(1)
        for j in range(1, count + 1):
            term *= -t*t / (2*j*(2*j-1))
            total += term
        return total
    return discretize(cosine_sum(PI_HI*q,11),cosine_sum(PI_LO*q,12))


def cos_pi(q):
    q %= 2
    q = min(q, 2-q)
    if q > Q(1,2):
        lo, hi = cosine_first_quadrant(1-q)
        return -hi, -lo
    return cosine_first_quadrant(q)


def kernel(y):
    w = (4*K*y)**2
    # Grid denominators avoid all three removable poles.
    q = (16*w-225)/((w-1)*(w-9)*(w-25))
    lo, hi = cos_pi(2*K*y)
    return discretize(min(q*lo,q*hi),max(q*lo,q*hi))


def abs_bounds(pair):
    lo, hi = pair
    return (0 if lo<=0<=hi else min(abs(lo),abs(hi))),max(abs(lo),abs(hi))


def check_integrals():
    h = Q(1,GRID)
    correction = 10*h*h  # |F''| < (2*pi*K)^2 < 80
    prev = kernel(Q(0))
    norm = logmoment = Q(0)
    for j in range(1,8*GRID+1):
        right = j*h
        nxt = kernel(right)
        plo,phi = abs_bounds(prev)
        nlo,nhi = abs_bounds(nxt)
        norm += 2*h*((phi+nhi)/2+correction)
        if right <= 1:
            same_sign = min(prev[0], nxt[0]) > 0 or max(prev[1], nxt[1]) < 0
            lower = min(plo, nlo) if same_sign else 0
            logmoment -= 2*h*max(0,lower-correction)*log_bounds(1/right)[0]
        else:
            logmoment += 2*h*(max(phi,nhi)+correction)*log_bounds(right)[1]
        prev = nxt
    # For y >= 8 the rational prefactor is at most .05/y^4.
    norm += Q(1,30*8**3)
    logmoment += (log_bounds(8)[1]+Q(1,3))/(30*8**3)
    assert norm < Q(77825,100000), norm
    assert logmoment < -Q(1382,1000), logmoment
    # Exact tail integral using z=sin(pi*s/(2K)), G a polynomial in cos.
    # G(s) ds = (29+6z^2-35z^4) dz/48.
    zlo,zhi=cos_pi(Q(1,2)-1/(2*K))
    def primitive(z):
        return (29*z+2*z**3-7*z**5)/48
    b=2*(primitive(1)-primitive(zlo))
    assert b<Q(2354,100000)
    xlo,xhi=cos_pi(1/(2*K))
    gs=PI_HI/(96*K)*xhi**3*(64-35*xlo*xlo)
    assert gs<Q(11,100)
    print('Upper bounds for norm, log moment, shoulders, G(1):',
          *[round(float(q),9) for q in (norm,logmoment,b,gs)])


def check_ranges():
    first=3883853444451
    curvature = K**2 * (2*PI_HI**2 - 16*sum(
        Q(c,384*v*v) for c,v in ((418,1),(-27,3),(-7,5))))
    assert 0 < curvature < 5
    # Upper extremal obstruction at the start of the finite range.
    lo, hi = tenth_root(first)
    assert Q(19966,1000) < Q(11*first,10*(first+1))*lo
    assert Q(11*(first+1),10*first)*hi < Q(19968,1000)
    assert Q(28892,1000) < log_bounds(Q(10*first,11))[0]
    jmax = Q(1296,1000)
    m = 103_800_788_359
    delta_hi = Q(11,10*first)
    peak = 4-jmax
    possible_saving = 4*delta_hi*m*peak
    assert Q(19966,1000)-1/peak-4*delta_hi*m > 19
    lhs = jmax*Q(19968,1000)+log_bounds(2*peak)[1]+possible_saving
    assert lhs < Q(27885,1000)
    stop=43_098_247_415_995
    T=3*10**12
    # log 2pi e = 1+log(2pi); CMS Lemma 9.
    nt = T/(2*PI_HI)*(log_bounds(T/(2*PI_HI))[0]-1) - (
        Q(15,100)*log_bounds(T)[1]+3)
    def budget(n):
        return (Q(77825,100000)*log_bounds(Q(10*(n+1),11))[1]-Q(135,100)
                -(1-4*Q(2354,100000))*Q(11*n,10*(n+1))*tenth_root(n)[0])
    assert budget(stop) < 0
    n=stop-1
    lower_budget=(Q(77825,100000)*log_bounds(Q(10*(n+1),11))[0]-Q(135,100)
                  -(1-4*Q(2354,100000))*Q(11*n,10*(n+1))*tenth_root(n)[1])
    assert lower_budget>0
    i=first
    bins=0
    while i<stop:
        j=min(stop,i+i//1000)
        # F(y) >= 1 - 5 y^2 from the cosine transform.
        low_h=1-5*(Q(11*T,10*i)/(2*PI_LO))**2
        saved=Q(5,6)*low_h*Q(22,10*(j+1))*nt
        assert saved>budget(i),(i,j,float(saved),float(budget(i)))
        i=j
        bins+=1
    print('Negative deficit at',stop,'and phase threshold 1/6 verified on',bins,'bins.')


if __name__=='__main__':
    check_pi()
    check_integrals()
    check_ranges()
