"""Check the compact autocorrelation and the two bounded-factor thresholds."""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from functools import cache
from math import isqrt
from check_cutoffs import tenth_root

scale=10**32
def down(x):
    return Q((x*scale).__floor__(),scale)
@cache
def log_bounds(q):
    # All calls here have |log q|<80. Decimal.ln is correctly rounded,
    # and precision 54 also covers the relative error in the division.
    q=Q(q)
    with localcontext() as ctx:
        ctx.prec=54
        x=Decimal(q.numerator)/q.denominator
        a=Q(x.ln())
    t=down(a)
    return t-Q(1,scale),t+Q(2,scale)
def lowlog(q): return log_bounds(q)[0]
def highlog(q): return log_bounds(q)[1]

c=[16,33,49,64,77,87,94,99]+[100]*12+[99,94,87,77,64,49,33,16]
den=sum(v*v for v in c)
b=[Q(sum(x*y for x,y in zip(c,c[k:])),den) for k in range(28)]+[Q(0)]
assert all(b[i]>=b[i+1] for i in range(28)) and b[0]==1
J=Q(sum(c)**2,20*den)
def G_at(step):
    k,rem=divmod(step,500)
    if k>=28: return Q(0)
    return b[k]+(b[k+1]-b[k])*Q(rem,500)

def constants():
    # L0 = 1-gamma-log(2 pi). The indicated enclosure is much wider
    # than the known bounds .57721<gamma<.57722 and 6.28318<2 pi<6.28319.
    a,b0=Q('-.41510')-1,Q('-.41508')-1
    assert 1-Q('.57722')-highlog(Q('6.28319')) > a
    assert 1-Q('.57721')-lowlog(Q('6.28318')) < b0+Q('.00001')
    b0+=Q('.00001')
    ml,mh=a+lowlog(20),b0+highlog(20)
    for k in range(1,28):
        pl=(k+1)*lowlog(k+1)+(k-1)*lowlog(max(1,k-1))-2*k*highlog(k)
        ph=(k+1)*highlog(k+1)+(k-1)*highlog(max(1,k-1))-2*k*lowlog(k)
        ml-=b[k]*ph; mh-=b[k]*pl
    assert ml>Q('-1.7671') and mh<Q('-1.7667')
    charge=0
    for j in range(1,4001):
        v=Q(j,10000)
        diff=G_at(10000+j-1)-G_at(10000+j)
        off=lowlog(Q('19.96')*v)+Q('.85')
        L=35 if off>=0 else 31
        charge+=2*diff*4*L*v/(L+off)
    print('Pole, two-sided exterior charge, log moment:',float(J),float(charge),float(ml),float(mh))
    assert charge*(1+Q(1,10**10))**2<Q('.1264')

def H2lo(log_a,log_b):
    eps=Q('.002')
    assert log_b>log_a>1
    return (1-eps)*(log_b**2-log_a**2)/2-2*eps*log_a
def H1hi(log_a,log_b):
    eps=Q('.002')
    return (1+eps)*(log_b-log_a)+2*eps

def run(vmax,first,goal):
    last=33_298_909_830_357
    l=first; worst=10
    while l<=last:
        r=min(last,l*1001//1000)
        x,y=lowlog(l),highlog(r)
        a0=lowlog(Q('1.001'))+Q('2.2')*x-highlog(vmax)
        a1=highlog(Q('1.001'))+Q('2.2')*y-lowlog(vmax)
        assert a0>highlog(10**8)
        u0=lowlog(Q('1.29'))+x
        u1=highlog(Q('1.29'))+y
        h2=H2lo(a1,u0)+H2lo(highlog(Q('1.29')*r+12),lowlog(Q('3.87')*l))/2
        h1all=H1hi(a0,highlog(Q('3.87')*r))
        h1=H1hi(a0,u1)+H1hi(u0,highlog(Q('3.87')*r))/2
        Amin=x-highlog(Q('1.1'))-Q('1.769')
        Amax=highlog(Q(10*(r+1),11))-Q('1.765')
        pl=Q('1.1')*tenth_root(l)[0]*l/(l+1)
        ph=Q('1.1')*tenth_root(r+1)[1]*(r+1)/r
        # Average theta over two residue classes <= (theta(U)+theta(3U))/2.
        e=2*Q('1.000001')*J*Q('2.004')*Q('1.419')*(1+h1all/Amin)
        rad=Amax*Amax-h2+e
        root_upper=Q(isqrt((rad*10**20).__floor__())+1,10**10)
        assert pl>Q('19.96') and ph<25
        left=pl*(J-Q('.1264'))-Q('.00001')-root_upper
        assert left>0
        # Every cofactor power is <=vmax; bound its prime base by sqrt(vmax).
        # At most 13 small primes per fixed cofactor power in the enlarged support.
        sqrt_a=l*tenth_root(l)[0]
        cubic_bound=2_200_000 if vmax<=10**19 else 5_000_000
        assert cubic_bound**3>vmax
        err=Q('1.000001')*13*33*highlog(vmax)*(isqrt(vmax)+1+70*cubic_bound)/sqrt_a
        ratio=(Amin*left-err-Q('.000001'))/(ph*J*h1)
        if ratio<worst: worst=ratio
        if ratio<=goal:
            print('Failed bin',l,r,'lower relative excess',float(ratio))
            raise ValueError('Requested threshold too high')
        l=r+1
    print('Cofactor bound',vmax,'first n',first,'relative excess lower bound',float(worst))

if __name__=='__main__':
    constants()
    run(10**19,3_883_854_444_451,Q('.002'))
    run(2**64,3_883_854_444_451,Q('.028'))
    run(4*10**18,10**13,Q('.05'))
