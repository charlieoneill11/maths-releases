"""Bound semiprime counts on the flanks using convex costs for cofactor prime gaps."""
from fractions import Fraction as Q
from functools import cache
import gzip
import json
from math import isqrt
from pathlib import Path
import numpy as np

from check_bounded_factors import highlog,lowlog
import check_wheel_cofactors as wheel
from check_record_cofactors import CELLS, PHYSICAL
from check_twenty_mode_splice import FINE,Fpair,safe

UNITS=10**6
I64=2**63-1

@cache
def prices():
    with Path(__file__).with_name('cofactor_gap_prices.json').open() as fp:
        rows=json.load(fp)
    assert len(rows)==48
    assert all(270<=g<=900 and a>=0 for row in rows for g,a in row)
    return rows

@cache
def histogram():
    with gzip.open(Path(__file__).with_name('gap_histogram_4e18.gz'),'rt') as fp:
        data={}
        for line in fp:
            fields=line.split()
            if len(fields)>=3 and fields[0].rstrip('*').isdigit() and fields[2].isdigit():
                g=int(fields[0].rstrip('*'));n=int(fields[2])
                assert g not in data or data[g]==n==0
                data[g]=n
    assert len(data)==739 and max(data)==1476
    return {g:sum(max(0,b-g)*n for b,n in data.items()) for row in prices() for g,_ in row}

class FactorCounts:
    def __init__(self,low,high):
        self.low=low;self.high=high
        assert 10**8<low<high<10**19
        step=self.step=10**9
        log_high=lowlog(high)
        self.error=((isqrt(high)+1)/log_high*(Q('1.95')+Q('3.9')/log_high+Q('19.5')/log_high**2)).__ceil__()
        # Fixed integer primitive lower than the integral of 1/log q.
        slope=[int(UNITS/highlog(y+step)) for y in range(low,high+1,step)]
        assert (high-low+2*step)*max(slope)<I64
        self.slope=np.array(slope,dtype=np.int64)
        self.base=np.r_[np.int64(0),np.cumsum(self.slope*step)]

    def __call__(self,endpoint):
        index,rest=np.divmod(np.clip(endpoint,self.low,self.high)-self.low,self.step)
        return np.maximum(0,(self.base[index]+rest*self.slope[index])//UNITS-self.error)

def price_increments(tmax,terms):
    # The certificate charges floor(h), where h is the open-window width.
    t=np.arange(tmax+1,dtype=np.int64)
    if not terms: return t[:0],t[:0]
    min_gap=min(g for g,_ in terms)
    last=tmax//min_gap+2
    assert last*UNITS+tmax*sum(a for _,a in terms)<I64
    best=np.full_like(t,last*UNITS)
    for m in range(1,last+1):
        # m is one more than the number of strictly interior primes.
        # At most this many covering prime gaps suffice, allowing endpoint primes.
        candidate=np.full_like(t,(m-1)*UNITS)
        for gap,weight in terms:
            candidate+=weight*np.maximum(0,t-m*gap)
        best=np.minimum(best,candidate)
    # For larger m the price (m-1)*UNITS exceeds the minimum achieved at last.
    delta=np.diff(best)
    assert best[0]==0 and np.all(delta>=0)
    positive=np.flatnonzero(delta)
    return positive+1,delta[positive]

def bounded_sum(a,b):
    if not len(a): return 0
    # Bound all per-element products and all chunk sums before int64 reduction.
    limit=int(a.max())*int(b.max())
    assert limit<I64
    if not limit:return 0
    width=min(len(a),I64//limit)
    return sum(int(x) for x in np.add.reduceat(a*b,np.arange(0,len(a),width)))

def convex_gain(left,right,layers):
    _,wmin,wmax,low=wheel.geometry(left,right)
    counts=FactorCounts(low,wheel.HIST_MAX)
    tmax=7*wmin//(25*low)
    weight_Q=PHYSICAL*Q('2.2')*lowlog(left)/wmax
    costs=histogram(); terms=prices()
    increments=[price_increments(tmax,row) for row in terms]
    penalties=[sum(a*costs[g] for g,a in row) for row in terms]
    total=Q(0)
    for j,drop in layers:
        i=min(len(terms)-1,len(terms)*j//CELLS)
        t,delta=increments[i]
        width=7*wmin*j//(25*CELLS)
        assert width<I64
        points=counts(width//t)
        charge=bounded_sum(delta,points)
        total+=drop*max(0,2*charge-penalties[i])
    return weight_Q*total/UNITS

def evaluate(left,right):
    layers,shape,constant=wheel.common()
    charge=wheel.budget(shape,left,right,constant)
    records=wheel.record_gain(left,right,layers)
    convex=convex_gain(left,right,layers)
    k=safe(Fpair(Q(0),FINE)[0]-charge+records+convex)
    assert k*Q('.11')*wheel.tenth_root(left)[0]*left/(left+1)-Q('.761942143419865')>Q('1.4')
    print('slab',left,right,'charge',float(charge),'record',float(records),'convex',float(convex),'k',k,flush=True)
    if wheel.comparison(left,k)[0]>0: return left,k
    assert wheel.comparison(right,k)[0]>0
    l,r=left,right
    while r>l+1:
        m=(l+r)//2
        if wheel.comparison(m,k)[0]>0:r=m
        else:
            assert wheel.comparison(m,k)[1]<0
            l=m
    print('first passing:',r,flush=True)
    return r,k

SLABS=(
    (32_650_000_000_000,32_657_973_000_000,Q('.900989106668924'),32_654_728_287_294),
    (32_654_000_000_000,32_654_728_300_000,Q('.900989355101264'),32_654_591_385_176),
    (32_654_400_000_000,32_654_591_400_000,Q('.900989374141681'),32_654_580_892_712),
)
FINAL=32_654_578_787_390

def run():
    from check_low_zero_transport import transported
    from check_low_zero_cutoff import COUNT,HEIGHT

    previous=32_657_972_050_142
    for lo,hi,expected,root in SLABS:
        assert lo<=previous<=hi and evaluate(lo,hi)==(root,expected)
        previous=root
    lo,hi,k,raw=SLABS[-1]
    anchor=raw-2_100_000
    assert lo<FINAL<anchor<raw<hi
    low=transported(anchor,FINAL,FINAL)[0]
    corrected=wheel.comparison(FINAL,k)[0]+Q('2.2')*low/(FINAL+1)
    assert low>Q('1400961.44') and corrected>Q('2.99e-14')
    assert Q('2.2')/FINAL*COUNT*(2+Q('2.2')*HEIGHT)<Q('.34')
    assert Q('1.1')*HEIGHT/(6*FINAL)<Q('7e-9')
    # Two-sided bracket of the optimistic raw comparison with no shoulder charge.
    f0lo,f0hi=Fpair(Q(0),FINE)
    baseline=3_883_854_444_452
    crossing=6_532_364_528_949
    assert wheel.comparison(baseline,f0hi)[1]<Q('-.66947')
    assert wheel.comparison(crossing-1,f0hi)[1]<0<wheel.comparison(crossing,f0lo)[0]
    assert f0lo*Q('.11')*wheel.tenth_root(baseline)[0]*baseline/(baseline+1)>Q('.761942143419865')
    print('real-base cutoff',FINAL,'improvement',32_657_972_050_142-FINAL,'corrected margin',float(corrected),flush=True)

if __name__=='__main__':
    import sys
    if len(sys.argv)==3:
        evaluate(*map(int,sys.argv[1:]))
    else:
        assert len(sys.argv)==1
        run()
