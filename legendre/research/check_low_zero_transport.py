"""Bound Platt's low-ordinate deficit and its local change over real base intervals."""
import gzip
import hashlib
from fractions import Fraction as Q
from functools import cache
from pathlib import Path

from check_cutoffs import log_bounds
from check_low_zero_cutoff import COUNT, DATA, DIGEST, HEIGHT
from check_three_mode import PI_LO, PI_HI, UNIT, cos_pi

GRID=32768


@cache
def table():
    # All cosine endpoints are returned on the fixed UNIT denominator.
    pairs=[cos_pi(Q(2*j,GRID)) for j in range(GRID)]
    assert max(b-a for a,b in pairs)<Q('1e-16')
    return [int(UNIT*b) for a,b in pairs]


@cache
def phase_ticks(n):
    p=[Q('1.1')*s for s in log_bounds(n*(n+1))]
    scale,modulus=10**11,2**96
    m=(modulus*p[0]/(2*PI_HI*scale)).__floor__()
    assert modulus*p[1]/(2*PI_LO*scale)-m < 2
    values=table()
    raw=gzip.decompress(Path(__file__).with_name(DATA).read_bytes())
    assert len(raw)==5*COUNT and hashlib.sha256(raw).hexdigest()==DIGEST
    tc=ts=0
    ticks=14*scale
    for j in range(0,len(raw),5):
        d=int.from_bytes(raw[j:j+5],'little')
        assert d>2; ticks+=d
        i,v=divmod((ticks*m%modulus)*GRID,modulus)
        w=modulus-v
        tc+=w*values[i]+v*values[(i+1)%GRID]
        k=(i-GRID//4)%GRID
        ts+=ticks*(w*values[k]+v*values[(k+1)%GRID])
    assert ticks < HEIGHT*scale-2
    gammaerr=Q('1.00001e-11')
    err=Q('1e-16')+p[1]*gammaerr+2*PI_HI*2*HEIGHT*scale/modulus+(2*PI_HI)**2/(8*GRID**2)
    low=COUNT*(1-err)-Q(tc,modulus*UNIT)
    high=COUNT*(1+err)-Q(tc,modulus*UNIT)
    center=Q(ts,modulus*UNIT*scale)
    errderiv=COUNT*(gammaerr+HEIGHT*err)
    # S'(u)=sum gamma sin(gamma u), with the sign for 1-cos.
    deriv=max(abs(center-errderiv),abs(center+errderiv))
    print('Low ledger reference',n,'deficit interval',float(low),float(high),'absolute derivative bound',float(deriv),flush=True)
    return low,high,deriv


def transported(n,left,right):
    base=phase_ticks(n)
    difference=Q('2.2')*max(abs(n-left),abs(right-n))/min(left,n)
    error=base[2]*difference+COUNT*HEIGHT**2*difference**2/2
    return base[0]-error,base[1]+error
