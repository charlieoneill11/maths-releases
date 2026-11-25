"""Extend the twenty-mode cutoff using the exhaustive record-gap table as a cofactor sieve."""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path

from check_bounded_factors import lowlog, highlog
from check_cutoffs import tenth_root
from check_splice_shoulders import T, budget
from check_local_histogram import PHYSICAL, read_histogram, splice_gain
from check_twenty_mode_splice import FINE, SCALE, Fpair, curvature, nodes, shoulders, safe

# (upper height, maximum gap below that height). The last line is the
# exhaustive-range limit displayed by the Record Gaps Between Primes project.
RECORDS = (
    (5_733_241_593_241_196_731, 1476), (6_787_988_999_657_777_797, 1488),
    (15_570_628_755_536_096_243, 1510), (17_678_654_157_568_189_057, 1526),
    (18_361_375_334_787_046_697, 1530), (2**64, 1550),
    (18_470_057_946_260_698_231, 1550), (18_571_673_432_051_830_099, 1552),
    (20_733_746_510_561_442_863, 1572), (68_068_810_283_234_182_907, 1676),
    (101_412_319_996_363_309_069, 1724), (132*10**18, 1854),
)
CELLS=3072
SUB=128
OLD = 32_791_000_993_425
NEW = 32_699_535_759_684
NORM = Q('.761942143419865')
MOMENT = Q('1.377680396761364')


def primary_layers():
    step=Q(7,25*CELLS)
    ns=nodes(CELLS,1/step,FINE)
    pad=Q('2e-12')+curvature(FINE)*step**2/8
    unit=10**12
    vals=[]
    for u,v in zip(ns,ns[1:]):
        val=max(0,((Q(min(u,v),T*SCALE)-pad)*unit).__floor__())
        vals.append(min(val,vals[-1]) if vals else val)
    return [(j+1,Q(u-v,unit)) for j,(u,v) in enumerate(zip(vals,vals[1:]+[0])) if u>v]


def record_gain(l,r,layers,records):
    rl=tenth_root(l)[0];rh=tenth_root(r+1)[1]
    amax=((r+1)*rh)**2
    amin=(l*rl)**2
    wmin=int(PHYSICAL*Q(11*l,10*(l+1))*l*rl**2)
    wmax=int(Q(11*(r+1),10*r)*(r+1)*rh**2)+1
    cap=amax*Q('1.000001')
    # This is exactly the histogram subtraction's lower q cutoff.
    right=(int(cap/(4*10**18-1500))//10**8+1)*10**8
    assert right<10**12 and amin*PHYSICAL/right > right+2000
    total=0
    for height, gap in records:
        left=(cap/(height-2000)).__ceil__()
        if left>=right:
            continue
        # For q in (left,right] each shoulder divided by q fits far inside
        # the listed record end; all these products survive the original sieve.
        assert left>2*10**8 and cap/left+gap<height
        llog,hlog=lowlog(right),highlog(left)
        reciprocal=lowlog(llog/hlog)-highlog(right)/(8*isqrt(left))
        count=(right-left)/lowlog(left)+Q(2*(isqrt(right)+1),24)*highlog(right)
        assert reciprocal>0 and count>0
        for j,diff in layers:
            width=wmin*Q(7*j,25*CELLS)
            total+=2*diff*max(0,width*reciprocal/gap-count)
        right=left
    return total*PHYSICAL*Q('2.2')*lowlog(l)/wmax


def comparison(n,k):
    root=tenth_root(n)
    m=Q(11*n,10*(n+1))*k
    arg=Q(10*(n+1),11)
    return (m*root[0]-NORM*highlog(arg)+MOMENT,
            m*root[1]-NORM*lowlog(arg)+MOMENT)


def prove(l,r,shape,layers,data,records):
    charge=budget(shape,l,r)
    hg=splice_gain(l,r,layers,data,cells=CELLS,sub=SUB,maximum=15*10**12,span=Q("2.56001"),tight_error=True)
    rg=record_gain(l,r,layers,records)
    coeff=safe(Fpair(Q(0),FINE)[0]-charge+hg+rg)
    print(l,r,'shoulder',float(charge),'histogram',float(hg),'record',float(rg),'k',coeff,flush=True)
    assert coeff*Q('.11')*tenth_root(l)[0]*l/(l+1)>NORM
    if comparison(l,coeff)[0]>0:return l,coeff
    assert comparison(l,coeff)[1]<0<comparison(r,coeff)[0]
    while r-l>1:
        n=(l+r)//2
        lo,hi=comparison(n,coeff)
        if lo>0:r=n
        else:
            assert hi<0
            l=n
    print('first passing:',r,'adjacent signs',float(comparison(l,coeff)[1]),float(comparison(r,coeff)[0]),flush=True)
    return r,coeff


def ancillary():
    # The original proof used x >= 32.75e12. Recheck every x-dependent
    # explicit-formula error over the complete extended slab.
    l,r=32_690_000_000_000,OLD
    d=Q('1.1')/l; dmin=Q('1.1')/(r+1)
    root=l*tenth_root(l)[0]
    pmax=Q('1.1')*(r+1)*tenth_root(r+1)[1]/r
    u=Q('1.000000000001')
    assert Q('2.5')*d < (u-1)/u
    assert 2*Q('1.1')*highlog(r+1)+1<71
    assert Q(71)/lowlog(2)<103 and 1+Q('2.5')*pmax*u<67
    powers=(103*67+2)*71*u/root
    zeros=2*d*((3+Q('.15')*highlog(7/dmin))*514+150)+10*d
    assert powers+zeros+Q('1e-9')+Q('1e-12')<Q('1e-8')


def run():
    ancillary()
    shape=shoulders(FINE);layers=primary_layers();data=read_histogram()
    cuts=(32_697_500_000_000,32_700_000_000_000,32_705_000_000_000,OLD)
    fine,k=prove(cuts[0],cuts[1],shape,layers,data,RECORDS)
    for left,right in zip(cuts[1:],cuts[2:]):
        assert prove(left,right,shape,layers,data,RECORDS)[0]==left
    conservative,_=prove(32_735_000_000_000,OLD,shape,layers,data,RECORDS[:6])
    print('Current-record and 2^64 cutoffs:',fine,conservative,flush=True)
    assert fine==32_699_537_863_134 and conservative==32_750_238_346_871
    assert k==Q('.900907850609657')
    assert Q('1.000000000974554')-164*Q('7e-9')**2>1
    from check_low_zero_cutoff import verify, DATA
    verify(Path(__file__).with_name(DATA),NEW,fine,k,NORM,MOMENT,Q(1))
    return NEW,conservative


if __name__=='__main__':run()
