"""Certify an optimized rational twenty-mode Fourier test at the high splice."""
from fractions import Fraction as Q
from functools import cache
from math import comb
from check_cutoffs import log_bounds,tenth_root
from check_three_mode import cos_pi,PI_LO,PI_HI
from check_bounded_factors import lowlog,highlog
from check_splice_shoulders import round_cos,budget,GRID,T,HEIGHT
from check_local_histogram import read_histogram,splice_gain,CELLS,LO,HI,SLICES
from check_splice_shoulders import FIRST,LAST

K=Q(5,2)
SCALE=10**9
COARSE=(380692119,249280290,84252442,-12648510,-23456728,-1700605,6786482,1646807,
   -1536599,-464975,212912,23782,-9192,2008,-2364,1342,-232,80,-49,35)
FINE=(380707290,249434692,84682233,-12031630,-23007900,-1646098,6624743,1562594,
      -1500312,-429738,210054,19455,-8325,1797,-2362,1271,-226,85,-52,26)

@cache
def modes(weights):
    return [(2*j+1,Q(a,SCALE)) for j,a in enumerate(weights)]
END=16
PANELS=256
H=Q(1,PANELS)
NODE_PREC=10**18

def Fpair(x,weights):
    M=modes(weights)
    for k,a in M:
        if 4*K*x==k: return K*a,K*a
    r=4*K*sum((-1)**(k//2)*k*a/(k*k-(4*K*x)**2) for k,a in M)
    lo,hi=cos_pi(2*K*x)
    vals=[r*v/p for v in (lo,hi) for p in (PI_LO,PI_HI)]
    return min(vals),max(vals)

@cache
def Fnode(j,weights):
    lo,hi=Fpair(Q(j,3*PANELS),weights)
    c=Q(((hi+lo)/2*NODE_PREC).__floor__(),NODE_PREC)
    assert max(hi-c,c-lo)<Q(1,10**14)
    return c

@cache
def lgy(j):
    from check_twelve_modes import signed_log
    return sum(signed_log(Q(j,PANELS)))/2

def logweights(j):
    # For s in [0,1], compute integrals of s^i log((j+s)h) for i<=3.
    # The cancellation amplifies endpoint log errors <1e-40 by <3*(1+j)^4.
    if j==0:
        J=[lgy(1)/(i+1)-Q(1,(i+1)**2) for i in range(4)]
    else:
        d=lgy(j+1)-lgy(j)
        J=[]
        for i in range(4):
            d=Q(1,i+1)-j*d
            J.append((lgy(j+1)-d)/(i+1))
    return [comb(3,i)*sum((-1)**k*comb(3-i,k)*J[i+k] for k in range(4-i))
            for i in range(4)]

def spectral(weights):
    M=modes(weights)
    der=(2*PI_HI)**4*2*K**5/5*sum(abs(a) for _,a in M)
    err=der*H**4/(24*81)+10*Q(1,10**14)
    mass=moment=0
    for j in range(END*PANELS):
        x,y,z,t=[Fnode(3*j+i,weights) for i in range(4)]
        b=[x,(-5*x+18*y-9*z+2*t)/6,(2*x-9*y+18*z-5*t)/6,t]
        assert max(map(abs,b))<10
        mass+=H*sum(map(abs,b))/2
        if j>=PANELS or min(b)>=0 or max(b)<=0:
            moment+=2*H*sum(a*v for a,v in zip(map(abs,b),logweights(j)))
    mass+=2*END*err
    moment+=2*(2+END*highlog(END))*err+Q('1e-18')
    rd=(Q(39,4*K*END))**2
    for i in range(4):
        r=2*i+1
        if i==3:
            shape=sum(k**r*abs(a) for k,a in M)/(1-rd)
        else:
            shape=abs(sum((-1)**(k//2)*k**r*a for k,a in M))
        c=shape/((4*K)**r*PI_LO)
        tail=2*c/(r*END**r)
        mass+=tail
        moment+=tail*(highlog(END)+Q(1,r))
    pole=Fpair(0,weights)[0]
    print('F0 lower, norm upper, moment upper (before ancillary errors):',
          float(pole),float(mass),float(moment),flush=True)
    return pole,mass,moment

def nodes(n,grid,weights):
    out=[0]*(n+1)
    assert n<=100000 and 12*Q('1e-18')*(n+1)<Q('2e-12')
    for k,a in enumerate(weights):
        arg=Q(2*k+1,2*K)
        x,y=round_cos(arg),round_cos(Q(1,2)-arg)
        step=arg/grid
        c,s=round_cos(step),round_cos(Q(1,2)-step)
        for i in range(n+1):
            out[i]+=a*x
            x,y=(c*x-s*y)//T,(s*x+c*y)//T
    assert sum(map(abs,weights))<SCALE
    return out

def curvature(weights):
    M=modes(weights)
    return sum(abs(a)*(PI_HI*k/(2*K))**2 for k,a in M)

def shoulders(weights):
    n=int((K-1)*GRID); ns=nodes(n,GRID,weights)
    pad=(HEIGHT*(Q('2e-12')+curvature(weights)/(8*GRID**2))).__ceil__()
    vals=[max(0,max(x,y)//1000+1+pad) for x,y in zip(ns,ns[1:])]
    stack=[(0,0)];strips={}
    for right,val in enumerate(vals+[0]):
        left=right
        while stack[-1][0]>val:
            old,left=stack.pop()
            dh=old-max(val,stack[-1][0])
            strips[right-left]=strips.get(right-left,0)+dh
        if val>stack[-1][0]:stack.append((val,left))
    assert sum(v*h for v,h in strips.items())==sum(vals)
    assert sum(strips.values())<Q('.14')*HEIGHT and max(strips)<GRID
    assert Q('2.5')*Q('1.1')/(32*10**12)<Q('1e-12')/Q('1.000000000001')
    return strips

def hist(weights,first,last,slices):
    delta=Q(7,25*CELLS)
    ns=nodes(CELLS,1/delta,weights)
    pad=Q('2e-12')+curvature(weights)*delta**2/8
    vals=[];unit=10**12
    for x,y in zip(ns,ns[1:]):
        val=max(0,((Q(min(x,y),T*SCALE)-pad)*unit).__floor__())
        vals.append(min(val,vals[-1]) if vals else val)
    layers=[(j+1,Q(x-y,unit)) for j,(x,y) in enumerate(zip(vals,vals[1:]+[0])) if x>y]
    excess=read_histogram()
    res=[]
    for k in range(slices):
        low=first+(last-first)*k//slices;high=first+(last-first)*(k+1)//slices
        res.append(splice_gain(low,high,layers,excess))
    print('Minimum cofactor subtraction',float(min(res)),flush=True)
    return min(res)

def safe(x,up=False):
    scale=10**15
    return Q((x*scale).__ceil__() if up else (x*scale).__floor__(),scale)

def slab(weights,first,last,slices,stats,strips,hist_first=None,hist_last=None):
    f0,norm,moment=stats
    charge=budget(strips,first,last)
    hl=first if hist_first is None else hist_first
    hr=last if hist_last is None else hist_last
    assert LO<=hl<=first<last<=hr<=HI
    gain=hist(weights,hl,hr,slices)
    coeff=safe(f0-charge+gain)
    norm=safe(norm,True);moment=safe(moment+Q('1e-8'),True)
    def bounds(n):
        l,r=tenth_root(n)
        z,t=log_bounds(Q(10*(n+1),11))
        p=coeff*Q(11*n,10*(n+1))
        return p*l-norm*t-moment,p*r-norm*z-moment
    assert coeff*Q('1.1')*Q('.1')*tenth_root(first)[0]*first/(first+1)>norm
    start_margin=bounds(first)[0]
    print('Safe constants k, norm, M+1e-8:',str(float(coeff)),str(float(norm)),str(float(moment)),flush=True)
    if start_margin>0:
        print('Whole slab positive, initial margin',float(start_margin),flush=True)
        return first
    assert bounds(first)[1]<0 and bounds(last)[0]>0
    l,r=first,last
    while r-l>1:
        n=(l+r)//2;a,b=bounds(n)
        if a>0:r=n
        else:
            assert b<0
            l=n
    print('Certified splice cutoff',r,'adjacent signs',float(bounds(l)[1]),float(bounds(r)[0]),flush=True)
    return r

def verify_shape(weights):
    M=modes(weights)
    s=sum(abs(v) for _,v in M)
    assert 2*K*s<4 and 2*PI_HI*K*K*s<32
    ksum=sum(k*abs(v) for k,v in M)
    lower=1-Q(39,4*K*END)**2
    assert 4*K/PI_LO*ksum*(2*PI_HI*K/lower+Q(2,END)/lower**2)/(4*K)**2<2
    return spectral(weights),shoulders(weights)

def ancillary():
    first=32_750_000_000_000
    d=Q('1.1')/first
    dmin=Q('1.1')/(LAST+1)
    root=first*tenth_root(first)[0]
    P=Q('1.1')*(LAST+1)*tenth_root(LAST+1)[1]/LAST
    u=Q('1.000000000001')
    assert Q('2.5')*d < (u-1)/u
    assert 2*Q('1.1')*highlog(LAST+1)+1<71
    assert Q(71)/lowlog(2)<103 and 1+K*P*u<67
    e=(103*67+2)*71*u/root
    assert 32*(16*highlog(16)-15)+2*(highlog(16)+1)/16<1000
    e+=2*d*((3+Q('.15')*highlog(7/dmin))*514+150)+10*d
    assert e+Q('1e-9')+Q('1e-12')<Q('1e-8')

def run():
    ancillary()
    stats,strips=verify_shape(COARSE)
    a=slab(COARSE,FIRST,LAST,SLICES,stats,strips,LO,HI)
    assert a==32_801_651_113_537
    stats,strips=verify_shape(FINE)
    left=32_750_000_000_000;split=32_810_000_000_000
    b=slab(FINE,left,split,1,stats,strips)
    assert slab(FINE,split,LAST,3,stats,strips)==split
    assert b==32_791_003_096_401 and left<b<a
    return a,b
if __name__=='__main__':run()
