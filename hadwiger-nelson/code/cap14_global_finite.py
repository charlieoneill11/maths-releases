"""Geometric forest and fixed-size crossing certificate, using exact rationals."""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
from tempfile import TemporaryDirectory
import json
import subprocess

from finite_polar import neighbours
from refit_wave_check import Hole

ROOT = Path(__file__).resolve().parent
PI_LO, PI_HI = F(333,106), F(355,113)


def area_count(R):
    # R is the normalized upper edge length, all points at mutual distance >1.
    if R*R <= 2:
        return 6
    if R <= F(39,25):
        return 8
    return None


def geometric_credits(profile, a, bins=65536, near_bins=8192):
    hole = Hole(profile)
    dt = F(73,10000*bins)
    weight = F(1)
    base = loss = near = F(0)
    for i in range(1,bins+1):
        t = dt*i
        weight = min(weight, hole.overlap(t,t*t/2))
        base += weight
        local = neighbours(t,a)
        planar = area_count(t/a)
        loss += weight * (min(planar,local) if planar else local)
    for i in range(near_bins):
        u,v = F(i,near_bins),F(i+1,near_bins)
        near += hole.overlap(2*a*(1-u*u)/(1+u*u),4*a*v/(1+v*v))*2*(v-u)/(1+v*v)
    def floor(z):
        return F(z*10**18//1,10**18)
    return floor(2*near/PI_HI),floor(2*base*dt/PI_HI),-floor(-loss*dt/PI_LO)


def graph(n,k,q,p,c,b,loss):
    slope = F(24*(n-2)*(n-3),(k-2)*(k-3))
    intercept = F(4*266*n*(n-1)*(n-2)*(n-3),9*k*(k-1)*(k-3))
    def variance(m):
        return n*(n-1)+intercept-slope*m-F(2,n)*m*m+m
    low,high = 0, n*n
    while high-low>1:
        mid=(low+high)//2
        if variance(mid)>=0:
            low=mid
        else:
            high=mid
    # Upper bound the real root by a rational on the concave tangent at low.
    u = low+variance(low)/(slope+F(4*low,n)-1)
    assert low<=u<=high and variance(u)<=0
    derivative = slope+4*u/n-1
    assert derivative>0 and p>b>0
    v = derivative*b*b/(2*(p-b))
    margin = c+loss-2*u*b/n-v
    penalty = n*min(0,margin)**2/(4*v)
    upper=n*(q+loss)+u*(p-b)+penalty
    return dict(n=n,k=k,edge_ceiling=low,upper=str(upper),decimal=float(upper),
                discard_penalty=float(penalty))


def main():
    source=json.loads((ROOT/'finite_polar_result.json').read_text())
    profile=ROOT/source['profile']
    assert sha256(profile.read_bytes()).hexdigest()==source['sha256']
    spec=json.loads(profile.read_text())
    # Validate the projected wave's symmetry and geometric conditions in the
    # reference checker prior to replacing its integration by finer bins.
    from wave_independent import check
    assert F(check(spec,4096)['blank'])==F(source['blank'])
    with TemporaryDirectory() as directory:
        binary=Path(directory)/'angle'
        subprocess.run(['g++','-std=c++17','-O3',str(ROOT/'cap14_global_angle.cpp'),'-o',binary],check=True)
        def edge(n):
            fields=[n,spec['x']]
            for name in ('left','right'):
                fields.append(len(spec[name]))
                fields.extend(x for point in spec[name] for x in point)
            total=int(subprocess.check_output([binary],input=' '.join(map(str,fields)),text=True))
            return F(2*total,spec['x']*500000000000)/F(314159,100000)
        assert edge(4194304)==F(source['unit_conflict_upper'])
        p=edge(134217728)
    a=F(2759,1000000)
    c,b,loss=geometric_credits(spec,a)
    # Sufficient elementary bounds for the one-crossing-neighbor proof.
    R=F(39,25)
    h=F(5,8)
    assert h*h<1-(R/2)**2 and R-h<1
    xmin=F(7,20)
    assert xmin**2+(R-h)**2<1 and (R-2*xmin)**2+(R-2*h)**2<1
    out=dict(angular_bins=134217728,short_radius=str(a),edge_probability=str(p),
             short_credit=str(c),unit_credit=str(b),loss=str(loss))
    out['orders']=[graph(n,2090,F(source['blank']),p,c,b,loss) for n in (10664,10665,10666)]
    assert out['orders'][1]['decimal']<1<=out['orders'][2]['decimal']
    assert F(out['orders'][1]['upper'])<1<=F(out['orders'][2]['upper'])
    print(json.dumps(out,indent=2))

if __name__=='__main__':
    main()
