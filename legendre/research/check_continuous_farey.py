"""Continuous Farey-spacing bound with an independently chosen sieve radius."""
from fractions import Fraction as Q
from math import isqrt

from check_bounded_factors import lowlog, highlog
from check_cutoffs import tenth_root
from check_splice_shoulders import GRID,HEIGHT,U
from check_three_mode import PI_HI


LAMBDA=Q(83,100)
TAU=Q("1.316")*LAMBDA
ETA=Q("1.33252")


def integral_constant():
    """Lower Darboux bound for twice the smooth weight integral plus constants."""
    steps=32768
    precision=10**13
    total=0
    for j in range(steps):
        s=Q(j,steps)
        low=Q(2*steps,j+1)
        alpha=Q(1,4)
        if j:
            high=Q(2*steps,j)
            k=low.__floor__()
            if high<=k+1:
                alpha+=min((low-k)*(1-low+k),(high-k)*(1-high+k))/2
        u=TAU*(1-alpha*s)
        value=-u/(1+s*u)
        total+=(value*precision).__floor__()
    constant=lowlog(LAMBDA)+2*ETA+Q(2*total,steps*precision)
    assert constant>Q("1.1452")
    # Euler product for the divisor-function majorant for 2^omega(q)*(q/phi(q))^2.
    product=Q(1)
    for prime in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        product*=1+2*(Q(prime,prime-1)**2-1)/prime
    assert highlog(product)+Q(5,47) < lowlog(13)
    assert 26*(1+highlog(2*10**8))+6 < 530
    return constant


def derivative_error_constant():
    """Upper Riemann sum for w(1)+integral |w'(s)|/sqrt(s), with s=t^2."""
    m=2048
    unit=10**12
    acc=0
    for j in range(m):
        s0,s1=Q(j*j,m*m),Q((j+1)**2,m*m)
        v0,v1=Q(0),Q(1)
        if s0:
            left,right=2/s1,2/s0
            k=left.__floor__()
            if right<=k+1:
                v0,v1=left-k,right-k
        ami=Q(1,4)+min(v0*(1-v0),v1*(1-v1))/2
        ama=Q(3,8)
        slope=max(1-v0-ami*s0, v1+ama*s1-1)
        sup=2*TAU*slope/(1+TAU*s0*(1-ama*s1))**2
        acc+=(unit*sup).__ceil__()
    bound=1/(1+3*TAU/4)+Q(2*acc,m*unit)
    assert bound<Q("2.287")
    return bound


def squarefree_gain():
    """Mean-spacing savings from discarding denominator multiples of 4,9,25,49."""
    primes=[p for p in range(2,102) if all(p%d for d in range(2,isqrt(p)+1))]
    squared=sum(Q(1,p*p) for p in primes)+Q(1,101)
    assert squared<Q(".462")
    sum_density=Q(0)
    union_weight=Q(0)
    unused=Q(1)
    for p in [2,3,5,7]:
        weight=unused/(p*p)
        density=(1-Q(1,p))*(1-squared+Q(1,p*p))
        sum_density+=weight*density
        union_weight+=weight
        unused*=1-Q(1,p*p)
    # Integral of tau*s/[4(1+s)(1+tau*s)^2] by lower rectangles.
    integral=Q(0)
    unit=10**12
    for j in range(4096):
        l,r=Q(j,4096),Q(j+1,4096)
        f=TAU*l/(4*(1+r)*(1+TAU*r)**2)
        integral+=(f*unit).__floor__()
    lower=sum_density*integral/(4096*unit)
    assert lower>Q(".00491")
    # f(s)<=tau/4, and the set of f(s)>c is an interval.
    assert TAU*union_weight/4 < Q(".11")
    assert 62*13*(1+highlog(2*10**8))+12 < 16250
    return lower


def varying_denominator(z,constant):
    """Lower bound for 2H-log N; z is an integer lower bound on sqrt(lambda N)."""
    root=isqrt(z)
    variation=Q("2.44")*Q("2.287")/root
    eta_loss=ETA*TAU/z
    mean_cost=Q(530)*TAU/z
    base=constant-2*(variation+eta_loss+mean_cost)
    cleanup=Q(".00491")-Q(".11")*(Q(2,root)+Q(2,z))
    reduced=constant+2*(cleanup-variation-eta_loss-Q(16250)*TAU/z)
    return max(base,reduced)


def budget(strips,l,r,constant):
    root0=tenth_root(l)[0]
    lower=l*root0
    p=Q(11*l,10*(l+1))*root0
    smallL=Q("1.1")*lowlog(l)
    largeL=Q("1.1")*highlog(r+1)
    hi_root=tenth_root(r+1)[1]
    assert Q(11*(r+1),10*r)*hi_root*(r+1)*hi_root*U < 3*10**16
    assert LAMBDA*(3*10**16+1)<(2*10**8)**2
    assert 2*Q(".14")*2*largeL*U**2/lower<Q("1e-9")
    charge=0;unit=10**21
    old_fee=2*(1+PI_HI/4)*Q('2.44')
    for w,h in strips.items():
        v=Q(w,GRID)
        t=p*lower*v/U
        assert t>10**10
        n=t.__floor__()-1
        z0=isqrt(3*n//4)
        zz0=isqrt(z0)
        old=2*ETA*z0/(z0+1)-highlog(Q(16,3))-old_fee/zz0
        if z0>470000:
            old+=Q(".13723")-Q("3.151")/zz0
        else:
            old=max(old,Q(".8601"))
        z=isqrt((LAMBDA*n).__floor__())
        offset=lowlog(p*v)+max(old,varying_denominator(z,constant))-highlog(U)
        L=largeL if offset>=0 else smallL
        charge+=(unit*8*Q(h,HEIGHT)*L*v*U**3/(L+offset)).__ceil__()
    return Q(charge,unit)


if __name__=="__main__":
    c=integral_constant()
    print("Squarefree-only additional H:",float(squarefree_gain()))
    print("Variation bound:",float(derivative_error_constant()))
    print("Continuous asymptotic sieve denominator, lower bound:",float(c))
    for z in [100000,10**6,10**7,3*10**7]:
        print(z,float(varying_denominator(z,c)))
