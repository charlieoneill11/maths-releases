"""Check the finite Farey-spacing sieve constants and their conditional cutoffs."""
from fractions import Fraction as Q
from math import isqrt, prod

from check_cutoffs import log_bounds, tenth_root

BETA = Q(987, 1000)
N_SQUARE = 70_500_000_000_000
GRID = 1024
ROUND = 10**14


def sqrt_lower(x):
    return Q(isqrt((x.numerator * ROUND**2) // x.denominator), ROUND)


def weight(alpha, s):
    return 1 / (1 + BETA*s*(1-alpha*s))


def integral_lower(l, r, f, sqrt_z):
    # f increases. Each rectangle has a lower numerator and an upper denominator.
    step = (r-l)/GRID
    total = 0
    for j in range(GRID):
        s = l+j*step
        val = ROUND*step*f(s)/(s+step)
        total += val.numerator//val.denominator
    penalty = Q("2.44")/sqrt_z*f(r)*(1/sqrt_lower(l)+1/sqrt_lower(r))
    return Q(total, ROUND)-penalty


def farey_improvement(sqrt_z):
    assert 1 + Q(2,3)*(Q(109545,100000)) < Q("1.316")**2
    assert Q(109545,100000)**2 > Q(6,5)
    assert 9_699_690*23 > 200_000_000
    assert prod(Q(p-1,p) for p in [2,3,5,7,11,13,17,19]) > Q(1,6)
    assert max(Q(6*64,23500),Q(6*256,510510)) < Q(".017")
    assert max(Q(12*64,117500),Q(12*256,510510)) < Q(".0066")
    assert Q(2,117500) < Q(".0001")
    total = integral_lower(Q(".05"),Q(1),
                           lambda s:weight(Q(".233"),s)-1/(1+s),sqrt_z)
    total += integral_lower(Q(".25"),Q(1),
                            lambda s:weight(Q(".243"),s)-weight(Q(".233"),s),sqrt_z)
    old = Q(".243")
    for m, new in enumerate(map(Q, [".2883",".3233",".3483",".3633"]), 1):
        d = Q(m,10)
        assert Q(1,4)+(d-Q(".0001"))*(1-d+Q(".0001"))/2-Q(".0066") > new
        for k in range(2,8):
            l, r = 2/(k+1-d), 2/(k+d)
            assert Q(".25") < l < r < 1
            total += integral_lower(l,r,lambda s:weight(new,s)-weight(old,s),sqrt_z)
        old = new
    return 2*total


def exact_cutoff():
    # Base constants .976 and .98 are established by check_combined_sieve.py.
    for sqrt_z, old, target in [(685,Q(".976"),Q("1.108")),
                                (1300,Q(".98"),Q("1.114"))]:
        improved = old+farey_improvement(sqrt_z)
        assert improved > target
        print("Certified additive denominator:", float(improved), ">", float(target))
    coeff = (Q("1.00000063")-Q(".09586014")*39/(39+Q("1.114")-Q(".8601"))
             +Q(".00024702"))
    def margin(n):
        l,h = tenth_root(n)
        q,r = log_bounds(Q(10*(n+1),11))
        k = coeff*Q(11*n,10*(n+1))
        return k*l-Q(".765870")*r+Q("1.37957"), k*h-Q(".765870")*q+Q("1.37957")
    low,high=33*10**12,34*10**12
    assert margin(low)[1]<0<margin(high)[0]
    while high-low>1:
        n=(low+high)//2
        lo,hi=margin(n)
        if lo>0: high=n
        else:
            assert hi<0
            low=n
    assert Q("1.1")*tenth_root(high)[0]*high/(high+1)>Q("24.7")
    assert Q("1.1")*log_bounds(high)[0]>Q("34.2")
    print("First integer passing the new comparison:", high)

    s=Q("1.104915")
    lo,hi=3*10**12,4*10**12
    logN=log_bounds(N_SQUARE)
    while hi-lo>1:
        j=(lo+hi)//2
        if s*log_bounds(j)[0]>logN[1]: hi=j
        else:
            assert s*log_bounds(j)[1]<logN[0]
            lo=j
    coeff2=Q("1.00000063")-Q(".09574178")*37/(37+Q("1.108")-Q(".8601"))
    u=(hi+1)/s
    g=coeff2*N_SQUARE/u-Q(".765870")*log_bounds(u)[1]+Q("1.37957")
    q=Q(6,5)
    next_power=(N_SQUARE/hi)*(1+(s-1)*log_bounds(q)[0])*(q*lo/(q*lo+1))
    g2=(Q(".99998381")*s*next_power
        -Q(".85385123")*log_bounds((q*hi+1)/s)[1]+Q("1.52239"))
    assert g>0 and g2>0 and logN[0]>Q("31.8")
    assert logN[1]+s*log_bounds(q+1/Q(lo))[1]<Q("32.1")
    assert N_SQUARE/u>Q("22.5") and Q("22.5")*N_SQUARE*Q(".999999")/4000>3*10**11
    assert s*(s-1)*coeff2*N_SQUARE/(hi+1)>1 and s/lo<Q(4,10**13)
    assert (s-1)*log_bounds(10**15)[0]>log_bounds(35)[1]
    assert (s-1)*log_bounds(10**15)[1]<log_bounds(40)[0]
    print("Exponent 2.20983 comparison margins:",float(g),float(g2))


if __name__ == "__main__":
    exact_cutoff()
