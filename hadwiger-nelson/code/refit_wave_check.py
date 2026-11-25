"""Rigorous finite-order test of a refitted wave using the entire empty hole."""
import argparse
from bisect import bisect_right
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path

from finite_extension import evaluation
from wave_independent import check as check_geometry

S=10**12


class Hole:
    def __init__(self,profile):
        self.x=profile['x']
        low=[(y,w) for y,w in profile['left'] if y<=S//4]
        first=next(i for i,p in enumerate(low) if p[1]==0)
        positive=low[:first+1]
        assert all(b<=a for (_,a),(_,b) in zip(low,low[1:]))
        points=[(-y,w) for y,w in positive[:0:-1]]+positive
        self.y,self.w=map(tuple,zip(*points))

    def _width(self,z):
        i=bisect_right(self.y,z)-1
        if self.y[i]==z:return self.w[i]
        a,b=self.y[i:i+2]
        u,v=self.w[i:i+2]
        return (u*(b-z)+v*(z-a))//(b-a)

    def overlap(self,X,Y):
        # Coordinates passed as rationals in length units. Both displacement
        # components are rounded up because of separate monotonicity.
        dx=-(-X*S//1);dy=-(-Y*S//1)
        lo=self.y[0]+dy;hi=self.y[-1]
        if lo>=hi or dx>=2*max(self.w):return F(0)
        cuts=sorted({lo,hi,*[y for y in self.y if lo<y<hi],
                     *[y+dy for y in self.y if lo<y+dy<hi]})
        # On each slab the minimum of three affine functions is concave.
        # Its chord is a lower bound and we integrate the positive part.
        def height(z):
            u=self._width(z);v=self._width(z-dy)
            return min(2*u,2*v,u+v-dx)
        twice=0;v=height(lo)
        for a,b in zip(cuts,cuts[1:]):
            u,v=v,height(b);w=b-a
            if min(u,v)>=0: twice+=w*(u+v)
            elif max(u,v)>0: twice+=w*max(u,v)**2//abs(u-v)
        return F(twice,2*S*self.x)


def geometry_credits(hole,a,w=F(73,10000),steps=512):
    delta=w/steps
    B=L=0
    # Take the running minimum because the numerical lower bounds are
    # allowed to dip below the exact monotone covariogram.
    h=F(1)
    for j in range(1,steps+1):
        t=j*delta
        h=min(h,hole.overlap(t,t*t/2))
        B+=h*delta
        k=0 if t<=a else ((1+2*t/a)**2//1)-1
        L+=h*delta*F(k,2)
    C=0
    for j in range(steps):
        u,v=F(j,steps),F(j+1,steps)
        dx=2*a*(1-u*u)/(1+u*u)
        dy=4*a*v/(1+v*v)
        C+=hole.overlap(dx,dy)*2*(v-u)/(1+v*v)
    floor=lambda q:F(q*10**15//1,10**15)
    return floor(C*F(7,11)),floor(B*F(7,11)),-floor(-L*F(100,157))


def certify(path,bins=4194304,precomputed=None):
    spec=json.loads(path.read_text())
    raw=check_geometry(spec,bins) if precomputed is None else precomputed
    q,p=F(raw['blank']),F(raw['conflict'])
    h=Hole(spec)
    good=None
    for j in range(260,310):
        a=F(j,100000)
        credits=geometry_credits(h,a)
        lo,hi=10400,11000
        while hi-lo>1:
            mid=(hi+lo)//2
            result=evaluation(mid,None,q,p,a,credits)
            if result is not None and F(result['upper'])<1:lo=mid
            else:hi=mid
        result=evaluation(lo,None,q,p,a,credits)
        if result is not None and F(result['upper'])<1 and (good is None or
           (result['vertices'],-F(result['upper']))>(good['vertices'],-F(good['upper']))):
            good=result
    assert good is not None
    return dict(profile=path.name,sha256=sha256(path.read_bytes()).hexdigest(),
                angular_bins=bins,blank=str(q),unit_conflict_upper=str(p),verified=good)


if __name__=='__main__':
    pp=argparse.ArgumentParser(description=__doc__)
    pp.add_argument('profile',type=Path,nargs='?',default=Path('refit_wave_candidate.json'))
    pp.add_argument('--bins',type=int,default=4194304)
    a=pp.parse_args()
    print(json.dumps(certify(a.profile,a.bins),indent=2))
