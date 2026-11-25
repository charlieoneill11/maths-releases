"""Exact enclosures for a twelve-cosine prime-interval test."""
from fractions import Fraction as Q
from decimal import Decimal, localcontext
from check_three_mode import PI_LO, PI_HI, cos_pi, discretize, abs_bounds
from check_cutoffs import log_bounds, tenth_root

W = (462994,232962,17574,-31174,472,7016,-1460,-974,377,-20,3,-11)
M = [(2*j+1,Q(a,10**6)) for j,a in enumerate(W)]


def F(y):
    for k,a in M:
        if 8*y==k:
            return 2*a,2*a
    scale = 8*sum((-1)**(k//2)*k*a/(k*k-(8*y)**2) for k,a in M)
    c=cos_pi(4*y)
    terms=[scale*v/p for v in c for p in (PI_LO,PI_HI)]
    return discretize(min(terms),max(terms))


def upper_shoulder(s):
    vals=[(a,cos_pi(k*s/4)) for k,a in M]
    return max(0,sum(max(a*l,a*h) for a,(l,h) in vals))


def signed_log(value):
    # All arguments supplied are ratios of integers at most 10^7, or
    # positive integers. The rounded numerator division perturbs the log by
    # < 2e-39, and the correctly rounded decimal log adds < 1e-38.
    with localcontext() as ctx:
        ctx.prec=48
        a=Decimal(value.numerator)/Decimal(value.denominator)
        v=Q(a.ln())
        return v-Q(1,10**40), v+Q(1,10**40)


def verify():
    assert sum(abs(a) for k,a in M)<Q(76,100)
    assert sum(abs(a)*(PI_HI*k/4)**2 for k,a in M)<16
    grid=4000
    step=Q(1,grid)
    corr=Q(161,8)*step**2
    assert (2*PI_HI)**2*Q(16,3)*sum(abs(a) for k,a in M)<161
    lpair=F(0)
    norm=moment=prev_log=0
    for j in range(1,16*grid+1):
        y=j*step
        pair=F(y)
        llo,lhi=abs_bounds(lpair)
        rlo,rhi=abs_bounds(pair)
        norm+=step*(lhi+rhi+2*corr)
        lg_low,lg_high=signed_log(y)
        av_upper=j*lg_high-(j-1)*prev_log-1
        if y>1:
            moment+=2*step*(max(lhi,rhi)+corr)*av_upper
        elif min(lpair[0],pair[0])>0 or max(lpair[1],pair[1])<0:
            moment+=2*step*max(0,min(llo,rlo)-corr)*min(0,av_upper)
        prev_log=lg_low
        lpair=pair
    c2=8*abs(sum((-1)**(k//2)*k*a for k,a in M))/(64*PI_LO)
    c4=8*sum(abs(a)*k**3 for k,a in M)/(4096*PI_LO*(1-Q(23,128)**2))
    for p,c in [(1,c2),(3,c4)]:
        mass=2*c/(p*16**p)
        norm+=mass
        moment+=mass*(log_bounds(16)[1]+Q(1,p))
    boxes=[(Q("24.7"),Q("34.2"),Q("34.4")),(Q("22.5"),Q("31.8"),Q("32.1"))]
    charges=[0,0]
    prev=upper_shoulder(2)
    maximum=Q(0)
    for j in range(grid,0,-1):
        u=j*step
        new=upper_shoulder(1+(j-1)*step)
        bound=max(max(prev,new)+2*step**2,maximum)
        diff=bound-maximum
        if diff>0:
            for i,(P,l,h) in enumerate(boxes):
                off=signed_log(P*u)[0]+Q(".86")
                ll=h if off>=0 else l
                charges[i]+=2*diff*4*ll*u/(ll+off)
        maximum=bound;prev=new
    print("F(0), norm, log moment, shoulder masses",
          float(F(0)[0]),float(norm),float(moment),*[float(v) for v in charges],flush=True)
    assert F(0)[0]>Q("1.00000063")
    assert norm<Q(".765870") and moment+Q(".000002")<-Q("1.37957")
    for i,charge in enumerate(charges):
        print("Effective pole coefficient",i,float(F(0)[0]-charge*(1+Q(1,10**10))**2))
    assert F(0)[0]-charges[0]*(1+Q(1,10**10))**2>Q(".904139")
    assert F(0)[0]-charges[1]*(1+Q(1,10**10))**2>Q(".904257")
    return norm,moment,charges


def application():
    s=Q("1.1")
    def margin(n):
        tlo,thi=tenth_root(n)
        ulo,uhi=log_bounds((n+1)/s)
        k=Q(".904139")*s*n/(n+1)
        return k*tlo-Q(".765870")*uhi+Q("1.37957"),k*thi-Q(".765870")*ulo+Q("1.37957")
    lo,hi=33*10**12,34*10**12
    while hi-lo>1:
        q=(hi+lo)//2
        a,b=margin(q)
        if a>0: hi=q
        else:
            assert b<0
            lo=q
    print("First integer satisfying the comparison",hi,flush=True)
    assert s*tenth_root(hi)[0]*hi/(hi+1)>Q("24.7")
    assert s*log_bounds(hi)[0]>Q("34.2")
    assert s*log_bounds(34_489_226_416_903)[1]<Q("34.4")
    s=Q("1.10494")
    N=70_500_000_000_000
    lo,hi=3*10**12,4*10**12
    while hi-lo>1:
        q=(hi+lo)//2
        if s*log_bounds(q)[0]>log_bounds(N)[1]: hi=q
        else:
            assert s*log_bounds(q)[1]<log_bounds(N)[0]
            lo=q
    u=(hi+1)/s
    gap=Q(".904257")*N/u-Q(".765870")*log_bounds(u)[1]+Q("1.37957")
    assert gap>Q(".0005")
    assert N/u>Q("22.5")
    assert log_bounds(N)[0]>Q("31.8") and log_bounds(N)[1]+s*log_bounds(Q(6,5)+1/Q(lo))[1]<Q("32.1")
    q=Q(6,5)
    nx=N/hi*(1+(s-1)*log_bounds(q)[0])*(q*lo/(q*lo+1))
    old=(Q(".99998381")*s*nx-Q(".85385123")*log_bounds((q*hi+1)/s)[1]+Q("1.52239"))
    print("Splice at exponent 2.20988",lo,hi,float(gap),float(old),flush=True)
    assert old>Q(".01")
    assert s*(s-1)*Q(".904139")*N/(hi+1)>1
    assert (s-1)*log_bounds(10**15)[0]>log_bounds(35)[1]
    assert 1/s*lo>Q(10**13,4)
    assert (s-1)*log_bounds(10**15)[1]<log_bounds(40)[0]

if __name__=='__main__':
    verify()
    application()
