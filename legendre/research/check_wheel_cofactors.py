"""Arithmetic wheel bounds for runs of bounded cofactor-prime gaps."""
from bisect import bisect_left
from functools import cache
from math import gcd, isqrt
from check_bounded_factors import lowlog, highlog
from check_record_cofactors import Q, CELLS, PHYSICAL, RECORDS, tenth_root, primary_layers, FINE, shoulders, comparison
from check_continuous_farey import budget, integral_constant


WHEEL=2*3*5*7*11*13
HIST_MAX=15*10**12
@cache
def geometry(left,right):
    root_lo=tenth_root(left)[0];root_hi=tenth_root(right+1)[1]
    cap=Q('1.000001')*((right+1)*root_hi)**2
    a_min=PHYSICAL*(left*root_lo)**2
    wmin=int(PHYSICAL*Q(11*left,10*(left+1))*left*root_lo**2)
    wmax=int(Q(11*(right+1),10*right)*(right+1)*root_hi**2)+1
    q0=(int(cap/(4*10**18-1500))//10**8+1)*10**8
    assert a_min/HIST_MAX>HIST_MAX+1476 and cap/q0+1476<4*10**18
    assert 2*a_min-Q('2.56001')*Q('1.000001')*wmax*HIST_MAX>1476*HIST_MAX*(HIST_MAX+2)
    assert 2*wmin/HIST_MAX>1476
    return cap,wmin,wmax,q0

class PrimeCount:
    """Lower cumulative integral on mesh plus a one-sided finite π discrepancy."""
    def __init__(self,low,high,step):
        assert 10**8<low<high<10**19
        self.low=low;self.high=high;self.step=step
        units=10**10
        self.units=units
        # Büthe, Theorem 2 (1.9),(1.10): 0 < li(x)-π(x) <= E(x).
        # Each positive summand sqrt(x)/log(x)^j is increasing for log(x)>2j.
        log_high=lowlog(high)
        self.error=((isqrt(high)+1)/log_high*(Q('1.95')+Q('3.9')/log_high+Q('19.5')/log_high**2)).__ceil__()
        self.slope=[];self.base=[0]
        for x in range(low,high+1,step):
            slope=int(units/highlog(x+step))
            self.slope.append(slope)
            self.base.append(self.base[-1]+step*slope)
        self.full=self(high)

    def __call__(self,end):
        if end<=self.low: return 0
        offset=min(end,self.high)-self.low
        i,rem=divmod(offset,self.step)
        return max(0,(self.base[i]+rem*self.slope[i])//self.units-self.error)

@cache
def wheel_bounds(gap,max_steps):
    # Greedy maximal endpoint from each coprime residue. The largest coprime
    # at or below x+gap is increasing in x and commutes with period translation.
    import numpy as np
    residues=np.arange(WHEEL,dtype=np.int64)
    coprime=np.gcd(residues,WHEEL)==1
    good=residues[coprime]
    steps=np.full(WHEEL,-1,dtype=np.int64)
    steps[good]=good
    steps=np.maximum.accumulate(steps)
    steps[0]=-1                          # the previous period ends in residue -1
    assert np.all(steps>=-1) and max(residues-steps)<gap
    extended=residues+gap
    advances=extended//WHEEL*WHEEL+steps[extended%WHEEL]-residues
    pos=good.copy(); spans=[0]
    for k in range(1,max_steps+1):
        pos+=advances[pos%WHEEL]
        spans.append(int(np.max(pos-good)))
    assert all(a<b<=k*gap for k,(a,b) in enumerate(zip(spans,spans[1:]),1))
    return spans

def record_gain(left,right,layers):
    cap,wmin,wmax,high=geometry(left,right)
    total=Q(0)
    for height,gap in RECORDS:
        low=(cap/(height-2000)).__ceil__()
        if low>=high: continue
        assert low>2*10**8 and cap/low+gap<height
        count=PrimeCount(low,high,10**7)
        # Maximal distance to the preceding coprime residue is less than 100.
        assert max_wheel_gap()<100
        max_steps=1+(7*wmin)//(25*(low+1)*(gap-100))
        spans=wheel_bounds(gap,max_steps)
        for j,drop in layers:
            width_num=7*wmin*j-1
            width=width_num//(25*CELLS)
            full=bisect_left(spans,width//high+1)-1
            last=bisect_left(spans,width//(low+1)+1)-1
            assert 0<=full<=last<max_steps
            num=full*count.full
            for k in range(full+1,last+1):
                num+=count(width//spans[k])
            total+=drop*2*num
        high=low
    return total*PHYSICAL*Q('2.2')*lowlog(left)/wmax

@cache
def max_wheel_gap():
    good=[i for i in range(WHEEL) if gcd(i,WHEEL)==1]
    return max(b-a for a,b in zip(good,good[1:]+[WHEEL+good[0]]))

@cache
def common():
    return primary_layers(),shoulders(FINE),integral_constant()
