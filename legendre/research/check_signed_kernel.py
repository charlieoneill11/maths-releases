"""Rigorous bounds for a six-cosine Fourier test at exponent 11/5."""
from decimal import Decimal, localcontext
from fractions import Fraction as Q

from check_three_mode import cos_pi, PI_LO, PI_HI, abs_bounds, discretize
from check_cutoffs import log_bounds, tenth_root

GRID = 2000
MODES = tuple(zip(range(1, 12, 2), [Q(i, 100000) for i in (51467,26561,2237,-3385,-87,534)]))


def spectrum(y):
    y=Q(y)
    for k, a in MODES:
        if 8*y == k:
            return 2*a, 2*a
    s = sum((-1)**(k//2)*k*a/(k*k-(8*y)**2) for k,a in MODES)
    c = cos_pi(4*y)
    out = [8*s*t/pi for t in c for pi in (PI_LO,PI_HI)]
    return discretize(min(out),max(out))


def shoulder(t):
    t=Q(t)
    low = high = 0
    for k,a in MODES:
        v,w=cos_pi(k*t/4)
        low+=min(a*v,a*w)
        high+=max(a*v,a*w)
    return max(low,0),max(high,0)


def log_node(j):
    # Decimal.ln is correctly rounded. j/GRID is an exact finite decimal.
    with localcontext() as ctx:
        ctx.prec=40
        value=Q((Decimal(j)/GRID).ln())
        return value-Q(1,10**38),value+Q(1,10**38)


def check():
    h=Q(1,GRID)
    # ||F''||∞ <= (4π)^2*4*sum |a_k| < 550.
    err=Q(550,8)*h*h
    f0=spectrum(0)
    left=f0
    norm=moment=0
    for j in range(1,12*GRID+1):
        right=spectrum(j*h)
        pl,ph=abs_bounds(left)
        ql,qh=abs_bounds(right)
        norm+=2*h*((ph+qh)/2+err)
        log_lo,log_hi=log_node(j)
        if j<=GRID:
            same=(left[0]>0 and right[0]>0) or (left[1]<0 and right[1]<0)
            moment+=2*h*max(0,min(pl,ql)-err)*min(0,log_hi) if same else 0
        else:
            moment+=2*h*(max(ph,qh)+err)*log_hi
        left=right
    # Expand k/(k²-(8y)²) at infinity, retaining the cancellation.
    C2=8/PI_LO*abs(sum((-1)**(k//2)*k*a for k,a in MODES))/64
    C4=8/PI_LO*sum(abs(a)*k**3 for k,a in MODES)/(1-Q(11,96)**2)/4096
    for r,c in [(1,C2),(3,C4)]:
        mass=2*c/(r*12**r)
        norm+=mass
        moment+=mass*(log_bounds(12)[1]+Q(1,r))
    # |G''| <= sum |a_k| (π k/4)² < 10.
    assert sum(abs(a)*(PI_HI*k/4)**2 for k,a in MODES)<10
    e=Q(10,8)*h*h
    left=shoulder(1)
    pos_mass=var=0
    # Upper-bound superset lengths via (G)_+ <= interpolant of endpoint positive parts +e.
    # Variation of (G)_+ <= variation of the positive-part chord + 10h² on each cell.
    for j in range(1,GRID+1):
        right=shoulder(1+j*h)
        pos_mass+=h*(left[1]+right[1]+2*e)
        var+=max(left[1]-right[0],right[1]-left[0])+10*h*h
        left=right
    print("F(0), norm, log-moment, exterior positive mass, one-side variation",*[round(float(a),8) for a in (f0[0],norm,moment,pos_mass,var)],flush=True)
    assert f0[0]>Q(110736425,10**8) and pos_mass<Q(2684511,10**8)
    assert var<Q(136973,10**6) and shoulder(1)[1]<Q(131968,10**6)
    assert (var+shoulder(1)[1])/2<Q(134471,10**6)
    assert norm<Q(85385123,10**8) and moment<-Q(15366567,10**7)
    assert moment+2*Q(53,1000)*Q(134471,10**6)+Q(2,10**6)<-Q(152239,10**5)
    def margin(n):
        lo,hi=tenth_root(n)
        l,u=log_bounds(Q(10*(n+1),11))
        k=(Q(110736425,10**8)-4*Q(2684511,10**8))*Q(11*n,10*(n+1))
        return (k*lo-Q(85385123,10**8)*u+Q(152239,10**5),
                k*hi-Q(85385123,10**8)*l+Q(152239,10**5))
    lo,hi=38*10**12,40*10**12
    while hi-lo>1:
        n=(lo+hi)//2
        low,high=margin(n)
        if low>0:
            hi=n
        else:
            assert high<0
            lo=n
    print("First integer satisfying the monotone cutoff inequality",hi)
    assert hi==38_296_393_337_347 and margin(hi)[0]>0 and margin(lo)[1]<0


if __name__=='__main__':
    check()
