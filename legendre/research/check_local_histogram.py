"""Certify a lower bound for the twelve-mode semiprime subtraction on 0<=u<=.28."""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import gzip

from check_bounded_factors import highlog, lowlog
from check_cutoffs import tenth_root
from check_twelve_modes import M, cos_pi

LO = 32_500_000_000_000
HI = 33_117_000_000_000
CELLS = 768
SLICES = 6
SUB = 16
MAX_Q = 10**13
BIN = 10**10
UNITS = 10**8
PHYSICAL = Q(".999999")
# Approximate optimizing choices, fixed as part of the proof. The lower bound
# holds for every cap and eta in (0,1]; no optimization assumption is used.
PROFILES = [
    (700,1),(650,1),(610,2),(580,2),(560,2),(534,3),(524,3),(514,3),
    (498,4),(490,4),(482,4),(482,4),(474,4),(466,5),(458,5),(458,5),
    (450,5),(450,5),(442,6),(434,6),(434,6),(434,6),(426,6),(426,6),
    (426,6),(410,8),(410,8),(410,8),(402,8),(402,8),(402,8),(402,8)
]


def read_histogram():
    path = Path(__file__).with_name("gap_histogram_4e18.gz")
    table = {}
    with gzip.open(path, "rt") as data:
        for line in data:
            fields = line.split()
            if len(fields) >= 3 and fields[0].rstrip("*").isdigit() and fields[2].isdigit():
                gap = int(fields[0].rstrip("*"))
                assert gap not in table or table[gap] == int(fields[2]) == 0
                table[gap] = int(fields[2])
    assert max(table)==1476 and len(table)==739
    return {cap:sum(max(0,g-cap)*v for g,v in table.items()) for cap,_ in PROFILES}


def shoulder_layers():
    # The lower step is rounded down, and monotonicity is enforced by prefix minima.
    unit = 10**12
    xstep = Q(7,25*CELLS)
    def knot(j):
        s=1+xstep*j
        result=Q(0)
        for k,a in M:
            lo,hi=cos_pi(k*s/4)
            result+=min(a*lo,a*hi)
        return result
    last=knot(0)
    levels=[]
    for j in range(1,CELLS+1):
        val=knot(j)
        floor=max(0,int(max(Q(0),min(last,val)-2*xstep**2)*unit))
        levels.append(min(floor,levels[-1]) if levels else floor)
        last=val
    return [(j+1,Q(l-r,unit)) for j,(l,r) in enumerate(zip(levels,levels[1:]+[0])) if l>r]


def pi_difference(q0,maximum=MAX_Q,tight_error=False):
    # Lower Riemann sum for the li-difference, piecewise linear in the upper end.
    # Schoenfeld gives total error <= 2 sqrt(Q) log(Q)/24 < 8,000,000.
    error=8_000_000
    end_errors=((isqrt(maximum)+1)*highlog(maximum)+(isqrt(q0)+1)*highlog(q0))/24
    if tight_error:
        error=end_errors.__ceil__()
    assert end_errors<=error
    base, slope = [0], []
    for l in range(q0,maximum+1,BIN):
        slope.append(int(UNITS/highlog(l+BIN)))
        base.append(base[-1]+BIN*slope[-1])
    def count(y):
        if y<=q0: return 0
        delta=min(maximum,y)-q0
        i,r=divmod(delta,BIN)
        return max(0,(base[i]+r*slope[i])//UNITS-error)
    return count


def splice_gain(lo,hi,layers,excess,*,cells=CELLS,sub=SUB,maximum=MAX_Q,span=4,tight_error=False):
    # Define W=aD=P sqrt(a). Trivial changes of scale and rounding are enclosed.
    rlo, rhi=tenth_root(lo)[0],tenth_root(hi+1)[1]
    a0=(lo*rlo)**2
    a1=((hi+1)*rhi)**2
    wmin=int(PHYSICAL*Q(11*lo,10*(lo+1))*rlo*(lo*rlo))
    wmax=int(Q(11*(hi+1),10*hi)*rhi*((hi+1)*rhi))+1
    q0=(int(a1*Q("1.000001")/(4*10**18-1500))//10**8+1)*10**8
    assert a1*Q("1.000001")/q0+1476<4*10**18
    ylo=a0*PHYSICAL
    shell=span*Q("1.000001")*wmax
    # q'-q>=2 gives joint separation across different q even between the two shoulders.
    assert 2*ylo-shell*maximum>1476*maximum*(maximum+2)
    assert 2*wmin/maximum>1476
    assert ylo/maximum>maximum+1476 and q0>2*10**8
    count=pi_difference(q0,maximum,tight_error)
    total=Q(0)
    for j,diff in layers:
        cap,eta10=PROFILES[min(31,32*j//cells)]
        # lower bound per cohort: k+(excess(q)/(cap eta)) >= min over integer counts.
        # sample the linear ramp's level variable at SUB right endpoints.
        total_p=0
        num=wmin*7*j*(10*sub)
        dem=25*cells*cap
        for k in range(1,1+num//(dem*10*sub*q0)):
            for t in range(1,sub+1):
                total_p+=count(num//(dem*(k*10*sub+t*eta10)))
        # Both shoulders contribute; all quotient prime gaps are disjoint.
        minimum=max(Q(0),Q(2*total_p,sub)-Q(10*excess[cap],cap*eta10))
        total+=diff*minimum
    logweight=PHYSICAL*Q(22,10)*lowlog(lo)
    return total*logweight/wmax


def run():
    excess=read_histogram()
    layers=shoulder_layers()
    values=[]
    for s in range(SLICES):
        lo=LO+(HI-LO)*s//SLICES
        hi=LO+(HI-LO)*(s+1)//SLICES
        v=splice_gain(lo,hi,layers,excess)
        values.append(v)
        print(lo,hi,float(v))
    print("Uniform normalized primary-lobe subtraction >",float(min(values)))
    assert min(values)>Q(".00036975")

if __name__=="__main__":
    run()
