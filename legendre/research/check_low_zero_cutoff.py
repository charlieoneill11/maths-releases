"""Prove the new twelve-mode cutoff from Platt's certified LMFDB zero intervals."""
from fractions import Fraction as Q
import gzip
import hashlib
import sys
from pathlib import Path
from check_cutoffs import log_bounds, tenth_root
from check_three_mode import PI_LO, PI_HI, UNIT, cos_pi, check_pi
from check_twelve_modes import F


COUNT = 1_400_000
HEIGHT = 816_393
DIGEST = 'e5c768ba7975c6c5a0c36de1e53328867b86353ed5188acfe301513764c7ba86'
DATA = 'platt_low_1400000.delta.gz'


# (target, previous uncorrected cutoff, pole coefficient, norm, log correction,
#  a lower bound for the signed transform on the inspected near-zero band)
ROWS = [
    (32_836_024_555_022, 32_836_026_647_689, Q('.90544226792447'),
     Q('.76582484235'), Q('1.37996409425'), Q(1)),
    (32_791_000_993_425, 32_791_003_096_401, Q('.900742352446013'),
     Q('.761942143419865'), Q('1.377680396761364'), Q(1)),
]


def verify(dataset,n,old,k,norm,moment,plateau):
    check_pi()
    pole=Q('1.1')*tenth_root(n)[0]*n/(n+1)
    baseline=k*pole-norm*log_bounds(Q(10*(n+1),11))[1]+moment
    assert pole>Q('24.7') and Q('1.1')*log_bounds(n)[0]>Q('34.2')
    assert k*pole/10-norm>Q('1.4')
    phase_lo,phase_hi=[Q('1.1')*x for x in log_bounds(n*(n+1))]
    modulus=2**96
    scale=10**11
    slope=(modulus*phase_lo/(2*PI_HI*scale)).__floor__()
    assert modulus*phase_hi/(2*PI_LO*scale)-slope < 2
    grid=32768
    cos_bounds=[cos_pi(Q(2*j,grid)) for j in range(grid+1)]
    endpoint_width=max(hi-lo for lo,hi in cos_bounds)
    assert endpoint_width<Q('1e-16')
    upper_cos=[int(UNIT*hi) for lo,hi in cos_bounds]
    with gzip.open(dataset,'rb') as data:
        raw=data.read()
    assert len(raw)==5*COUNT and hashlib.sha256(raw).hexdigest()==DIGEST
    total_upper=0
    ticks=14*scale
    for pos in range(0,len(raw),5):
        delta=int.from_bytes(raw[pos:pos+5],'little')
        assert delta>2
        ticks+=delta
        phase=ticks*slope%modulus
        j,r=divmod(phase*grid,modulus)
        total_upper+=(modulus-r)*upper_cos[j]+r*upper_cos[j+1]
    assert ticks<(HEIGHT*scale-2)
    # The display retains >=25 fractional decimals. Truncation to 11 places,
    # text-export rounding, and the underlying precision 2^-102 cost <1.00001e-11.
    angle_error=phase_hi*Q('1.00001e-11')+2*PI_HI*2*HEIGHT*scale/modulus
    interpolation=(2*PI_HI)**2/(8*grid**2)
    lower=COUNT*(1-interpolation-angle_error)-Q(total_upper,modulus*UNIT)
    corrected=baseline+plateau*Q(22,10*(n+1))*lower
    assert corrected>Q('1e-15')
    upper=COUNT*(1+interpolation+angle_error+endpoint_width)-Q(total_upper,modulus*UNIT)
    g_upper=k*Q('1.1')*tenth_root(n)[1]*n/(n+1)-norm*log_bounds(Q(10*(n+1),11))[0]+moment
    h_upper=g_upper+plateau*Q(22,10*(n+1))*upper
    assert h_upper<Q('5e-14')
    derivative_lower=k*Q('1.1')*tenth_root(n-1)[0]*(n-1)/(10*n)-norm
    assert derivative_lower>Q('1.4')
    derivative_cost=Q('2.2')/n*COUNT*(2+Q('2.2')*HEIGHT)
    previous_upper = h_upper-(derivative_lower-derivative_cost)/n
    assert derivative_cost<Q('.34')
    assert Q('1.1')*HEIGHT/(n*6)<Q('7e-9')
    print('Phase sum lower bound:',float(lower))
    print('Corrected comparison lower bound:',float(corrected))
    print('Real-base cutoff:',n,'reduction:',old-n)
    print('Previous-base margin upper bound:',float(previous_upper))
    # Distinguish the positive-band phase contraction from scalar tent transfer.
    assert max(F(Q(j,1000))[1] for j in range(820,861)) < Q('-.064')
    assert Q('.064')>39*Q('.0005')
    assert cos_pi(Q('.36'))[0]**2/(PI_HI*Q('.86'))**2>Q('.02')
    dhi=Q('3e-13')
    assert Q('.04')*log_bounds(Q('.82')/dhi)[0]-Q(20)*dhi>Q('1.13')


def compare_source_pages(folder):
    """Check the archived coding from official raw ASCII files named FIRST.txt."""
    previous=14*10**11
    compact=hashlib.sha256()
    next_index=1
    manifest=Path(__file__).with_name('platt_low_1400000.tsv')
    for row in manifest.read_text().splitlines()[1:]:
        start,length,digest,url=row.split('\t')
        start,length=int(start),int(length)
        assert url==f'https://www.lmfdb.org/zeros/zeta/list?N={start}&limit={length}&fmt=plain'
        assert start==next_index
        raw=(folder/f'{start}.txt').read_bytes()
        assert hashlib.sha256(raw).hexdigest()==digest
        lines=raw.splitlines()
        assert len(lines)==length
        for line in lines:
            index,value=line.split()
            whole,frac=value.split(b'.')
            assert int(index)==next_index and len(frac)>=25
            next_index+=1
            tick=int(whole)*10**11+int(frac[:11])
            compact.update((tick-previous).to_bytes(5,'little'))
            previous=tick
    assert next_index==COUNT+1 and compact.hexdigest()==DIGEST
    print('Source pages match the compact archive.')


if __name__=='__main__':
    if len(sys.argv)==3 and sys.argv[1]=='--compare-source-pages':
        compare_source_pages(Path(sys.argv[2]))
    elif len(sys.argv)!=1:
        raise SystemExit('usage: check_low_zero_cutoff.py [--compare-source-pages DIRECTORY]')
    assert Q('1.000000000974554')-Q(328,2)*Q('7e-9')**2>ROWS[1][-1]
    for row in ROWS:
        verify(Path(__file__).with_name(DATA),*row)
