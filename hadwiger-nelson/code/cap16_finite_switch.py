"""Exact nested-forest certificate allowing unit edges to replace short edges."""
from fractions import Fraction as F
from math import isqrt,lcm
from pathlib import Path
import json
from cap15_finite_nested import credits,up,down,S
from cap14_global_finite import PI_HI
from refit_wave_check import Hole
ROOT=Path(__file__).resolve().parent

def geometry(a,d,bins=65536,spec=None):
    g=credits(a,d,bins,spec)
    if spec is None:spec=json.loads((ROOT/'refit_wave_candidate.json').read_text())
    hole=Hole(spec)
    weight=F(1); hs=[]
    step=F(73,10000*bins)
    for k in range(1,bins+1):
        t=k*step
        weight=min(weight,hole.overlap(t,t*t/2))
        hs.append(weight)
    for r,name in [(a,'first'),(d,'second')]:
        max_short=F(0)
        for k in range(8192):
            u,v=F(k,8192),F(k+1,8192)
            w=hole.overlap(2*r*(1-u*u)/(1+u*u),4*r*v/(1+v*v))
            max_short=max(max_short,w)
        # The same h is used for the unit credit and the bonus. Pi cancels.
        rho=sum(max(F(0),h-max_short) for h in hs)/sum(hs)
        g[name+'_retained_per_mille']=rho*1000//1
        g[name+'_max_short']=str(max_short)
    return g

def verify(n,g):
    g0=json.loads((ROOT/'finite_polar_result.json').read_text())
    g1=json.loads((ROOT/'cap14_global_finite_result.json').read_text())
    q,p=up(F(g.get('blank',g0['blank']))),up(F(g.get('edge_probability',g1['edge_probability'])))
    b,c,e,L,T,U,K,J=(g[z] for z in ('B','C','E','L','T','U','K','J'))
    first,second=(g[z+'_retained_per_mille'] for z in ('first','second'))
    k=2090
    slope=F(24*(n-2)*(n-3),(k-2)*(k-3))
    const=F(4*266*n*(n-1)*(n-2)*(n-3),9*k*(k-1)*(k-3))
    quad=[F(-2,n),1-slope,n*(n-1)+const]
    den=lcm(*(x.denominator for x in quad))
    aa,bb,cc=[int(x*den) for x in quad]
    def variance_num(m):return (aa*m+bb)*m+cc
    ceiling=(isqrt(bb*bb-4*aa*cc)+bb)//(-2*aa)
    assert variance_num(ceiling)>=0>variance_num(ceiling+1)
    den_w=2000
    ws=2000-first
    stack=[((0,ceiling),(0,n),(0,n))]
    visited=0;largest=0
    while stack:
        box=stack.pop()
        (m,M),(s,v),(j,w)=box
        visited+=1
        if s+j>n:continue
        v,w=min(v,n-j),min(w,n-s)
        var=variance_num(m)
        def missed(wj):
            minsum=ws*s+wj*j
            maxsum=ws*v+wj*w
            square=ws*ws*v+wj*wj*w
            mean=(2*b*M*maxsum+n*den_w-1)//(n*den_w)
            norm=max(0,n*square-minsum**2)
            return mean+1+isqrt(2*b*b*var*norm//(den*n*den_w**2))
        base=n*q+M*(p-b)-s*c-j*e
        cost=min((n-s)*L,(n-s)*T+w*U,(n-s-j)*K+w*J)
        val=min(n*q+M*p,base+missed(1000-second)+cost,
                base+missed(2000-second)+(n-s-j)*K)
        if val<S:
            largest=max(largest,val)
            continue
        widths=[M-m,12*(v-s),12*(w-j)]
        i=widths.index(max(widths))
        if widths[i]==0:
            return dict(n=n,proved=False,m=m,s=s,j=j,upper=val,boxes=visited)
        box=((m,M),(s,v),(j,w))
        low,hi=box[i];mid=(low+hi)//2
        for span in ((low,mid),(mid+1,hi)):
            stack.append(box[:i]+(span,)+box[i+1:])
    return dict(n=n,proved=True,edge_ceiling=ceiling,boxes=visited,largest_upper=largest)

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first',type=F,default=F('.00265'))
    parser.add_argument('--second',type=F,default=F('.0044'))
    parser.add_argument('--bins',type=int,default=65536)
    parser.add_argument('--start',type=int,default=10674)
    parser.add_argument('--profile',type=Path,default=ROOT/'cap16_finite_wave.json')
    parser.add_argument('--angle-bins',type=int,default=67108864)
    args=parser.parse_args()
    from tempfile import TemporaryDirectory
    from wave_independent import check
    import hashlib,subprocess
    spec=json.loads(args.profile.read_text())
    coarse=check(spec,4096)
    with TemporaryDirectory() as directory:
        binary=Path(directory)/'angle'
        subprocess.run(['g++','-std=c++17','-O3',str(ROOT/'cap14_global_angle.cpp'),'-o',binary],check=True)
        def probability(bins):
            fields=[bins,spec['x']]
            for name in ('left','right'):
                fields.append(len(spec[name]))
                fields.extend(value for point in spec[name] for value in point)
            total=int(subprocess.check_output([binary],input=' '.join(map(str,fields)),text=True))
            return F(2*total,spec['x']*500000000000)/F(314159,100000)
        assert probability(4096)==F(coarse['conflict'])
        p=probability(args.angle_bins)
    g=geometry(args.first,args.second,args.bins,spec)
    g.update(blank=coarse['blank'],edge_probability=str(p),angle_bins=args.angle_bins,
             profile_sha256=hashlib.sha256(args.profile.read_bytes()).hexdigest())
    checks=[]
    for n in range(args.start,10800):
        r=verify(n,g)
        checks.append(r)
        if not r['proved']:break
    print(json.dumps(dict(geometry=g,checks=checks),indent=2))
