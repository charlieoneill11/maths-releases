"""Rational two-radius forest certificate. Run from any directory."""
from fractions import Fraction as F
from math import isqrt
from hashlib import sha256
from pathlib import Path
import json
from cap14_global_finite import area_count, PI_HI, PI_LO
from finite_polar import neighbours
from refit_wave_check import Hole
ROOT=Path(__file__).resolve().parent
S=10**18
def up(x): return -(-x*S//1)
def down(x): return x*S//1

def credits(a,d,bins,spec=None):
    if spec is None:
        path=ROOT/'refit_wave_candidate.json'
        previous=json.loads((ROOT/'finite_polar_result.json').read_text())
        assert sha256(path.read_bytes()).hexdigest()==previous['sha256']
        spec=json.loads(path.read_text())
    hole=Hole(spec)
    dt=F(73,10000*bins)
    base=tot=tail=near=big=local=0
    h=F(1)
    for i in range(1,bins+1):
        t=i*dt
        h=min(h,hole.overlap(t,t*t/2))
        base+=h
        ka,kd=neighbours(t,a),neighbours(t,d)
        ga=min(ka,area_count(t/a) or ka)
        gd=min(kd,area_count(t/d) or kd)
        tot+=ga*h
        local+=ka*h
        big+=gd*h
        if t<=d: near+=ka*h
        else: tail+=ga*h
    def short(r):
        cnt=8192
        val=0
        for i in range(cnt):
            u,v=F(i,cnt),F(i+1,cnt)
            val+=hole.overlap(2*r*(1-u*u)/(1+u*u),4*r*v/(1+v*v))*2*(v-u)/(1+v*v)
        return down(2*val/PI_HI)
    return dict(a=str(a),d=str(d),bins=bins,B=down(2*base*dt/PI_HI),C=short(a),E=short(d),
                L=up(tot*dt/PI_LO),T=up(tail*dt/PI_LO),U=up(2*near*dt/PI_LO),K=up(big*dt/PI_LO),J=up(2*local*dt/PI_LO))
def verify(n,g,*,edge_cap=None):
    k=2090
    geo=json.loads((ROOT/'cap14_global_finite_result.json').read_text())
    e=json.loads((ROOT/'finite_polar_result.json').read_text())
    q,p=up(F(e['blank'])),up(F(geo['edge_probability']))
    b,c,f,L,T,U,K=[g[x] for x in ('B','C','E','L','T','U','K')]
    # n * 9*k*(k-1)*(k-2)*(k-3) times V(m).
    scale=9*k*(k-1)*(k-2)*(k-3)*n
    slope=24*(n-2)*(n-3)*(scale//((k-2)*(k-3)))
    intercept=4*266*n*(n-1)*(n-2)*(n-3)*(scale//(9*k*(k-1)*(k-3)))
    def var(m):
        return scale*(n*(n-1)+m)+intercept-slope*m-2*m*m*(scale//n)
    hi=n*n;lo=0
    while hi-lo>1:
        m=(lo+hi)//2
        if var(m)>=0:lo=m
        else:hi=m
    ceiling = lo if edge_cap is None else min(lo,edge_cap)
    stack=[((0,ceiling),(0,n),(0,n))]
    boxes=0;worst=0
    while stack:
        box=stack.pop();(m,M),(s,v),(j,w)=box
        boxes+=1
        if s+j>n: continue
        def excluded(low,high):
            high=min(high,n)
            peak=min(max(n//2,low),high)
            num=2*var(m)*peak*(n-peak)
            if n%2 and low<=n//2+1<=high:num=max(num,2*var(m)*(n//2+1)*(n//2))
            return b*((2*M*high+n-1)//n+isqrt(num//(scale*n))+1)
        base=n*q+M*(p-b)
        loss=min((n-s)*L,(n-s)*T+w*U,(n-s-j)*K+w*g["J"])
        v1=base-s*c+excluded(s,v)+loss
        v2=base-s*c-j*f+excluded(s+j,v+w)+(n-s-j)*K
        # Retain heads from the larger roots and tails from the smaller roots.
        # Missing oriented incidences have weights 1 and 1/2 on the two layers.
        norm4=max(0,4*n*v+n*w-(2*s+j)**2)
        mix=b*((M*(2*v+w)+n-1)//n+isqrt((var(m)*norm4)//(2*n*scale))+1)
        v3=base-s*c-j*f+mix+loss
        val=min(v1,v2,v3,n*q+M*p)
        if val<S:
            worst=max(worst,val);continue
        widths=[(h-l)*cost for (l,h),cost in zip(box,(1,12,12))]
        axis=widths.index(max(widths)); l,h=box[axis]
        if h==l:return dict(n=n,proved=False,box=box,upper=val,boxes=boxes)
        mid=(l+h)//2
        for part in ((l,mid),(mid+1,h)):
            stack.append(box[:axis]+(part,)+box[axis+1:])
    return dict(n=n,proved=True,boxes=boxes,worst_upper=worst)
if __name__=='__main__':
    import sys
    if len(sys.argv)>1:
        saved=json.loads(Path(sys.argv[1]).read_text())
        g=saved.get('geometry',saved)
    else:g=credits(F(259,100000),F(380,100000),65536)
    print(json.dumps(g),flush=True)
    for n in range(10672,10700):
        r=verify(n,g);print(json.dumps(r),flush=True)
        if not r['proved']:break
