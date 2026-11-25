"""Certified full-cone forest and a conditional bound on consecutive rhombi."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json

from hybrid_order import diamond_credits
from wave_order import diamond

CROSSING = F(1500, 41209)
PI_BELOW = F(157, 50)
PI_ABOVE = F(22, 7)
SCALE = 10**16


def floor_bound(q):
    return F(q*SCALE//1, SCALE)


def ceil_bound(q):
    return -floor_bound(-q)


def packed_credits(x,r,l,a,steps=280):
    support=F(7,1000)
    dt=support/steps
    volume=r*l/(x*F(1,2))
    credit=loss=F(0)
    last=volume
    for i in range(1,steps+1):
        t=i*dt
        u,v=t/r,t*t/(2*l)
        h=volume*max(0,1-(u+v)/2)*max(0,1-abs(u-v)/2)
        assert 0<=h<=last
        last=h
        # Two tails of eligible incoming edges have distance <= 2*t.
        # For each representative, pack the other representative centers
        # by disjoint disks of radius a inside its disk of radius 2*t+a.
        count=0 if t<=a else ((1+2*t/a)**2//1)-1
        credit+=h*dt
        loss+=h*dt*F(count,2)
    c,_=diamond_credits(x,F(1,2),r,l,a)
    return floor_bound(c),floor_bound(2*credit/PI_ABOVE),ceil_bound(2*loss/PI_BELOW)


def edge_test(n,dups,m):
    if dups is None:
        return 4*CROSSING*m**3/n**2
    return CROSSING*max(0,2*m-dups)**3/n**2


def evaluation(n,dups,q,p,angle,credits,close_pairs=None):
    c,b,loss=credits
    assert p>b>0 and c>0 and loss>=0
    # Below the relevant crossing-lemma threshold, the direct union suffices.
    sparse=F(677,100)*n if dups is None else (F(677,100)*n+dups)/2
    if n*q+sparse*p>=1:
        return None
    intersection_budget=n*(n-1) if close_pairs is None else 2*close_pairs
    def residual(m):
        return intersection_budget-edge_test(n,dups,m)-F(2*m*m,n)+m
    lo,hi=0,n*n
    while hi-lo>1:
        mid=(lo+hi)//2
        if residual(mid)>=0:
            lo=mid
        else:
            hi=mid
    # u is above the real root. Hence for admissible m, 0<=V(m)<=D*(u-m).
    u=hi
    D=(12*CROSSING*u*u/n**2 if dups is None
       else 6*CROSSING*max(0,2*u-dups)**2/n**2)+F(4*u,n)-1
    g=c-2*u*b/n-D*b*b/(2*(p-b))
    if g<0:return None
    bound=n*(q+loss)+u*(p-b)
    return dict(vertices=n,edge_ceiling=lo,edge_ceiling_plus_one=u,
                upper=str(bound),decimal=float(bound),margin_per_discard=str(g),
                cone_separation=str(2*angle),close_credit=str(c),
                unit_credit=str(b),loss_per_representative=str(loss))


def unit_credit_limit(spec,n,q,p,m):
    # Integrate the actual blank profile at zero vertical residual. Its
    # centered vertical slices maximize the overlap there for fixed dx.
    S=10**12
    x=F(spec['x'],S)
    left=[(F(t,S),F(v,S)) for t,v in spec['left']]
    r=max(v for t,v in left)
    assert 2*x-2*r>1 and r<F(1,100)
    active=[t for t,v in left if v>0 and t<F(1,4)]
    last=max(active)
    next_knot=min(t for t,v in left if t>last)
    assert next_knot<F(1,20)
    # Thus only the vertical center difference of length one can occur.
    square_integral=sum((t-s)*(a*a+a*b+b*b)/3
                        for (s,a),(t,b) in zip(left,left[1:]))
    upper=4*square_integral/(PI_BELOW*x*(1-4*r*r))
    lower=n*q+m*(p-upper)
    return dict(n=n,aggregate_edge_ceiling=m,mean_unit_double_hit_upper=str(upper),
                aggregate_lower=str(lower),aggregate_decimal=float(lower))


def run():
    geo=json.loads(Path('wave_order.json').read_text())[1]
    path=Path(geo['file'])
    assert sha256(path.read_bytes()).hexdigest()==geo['sha256']
    spec=json.loads(path.read_text())
    q=F(geo['blank']);p=max(F(geo[k]) for k in ('independent_probability','profile_probability'))
    x=F(spec['x'],10**12)
    r,l=diamond(spec)
    params=[]
    for j in range(240,291):
        a=F(j,100000)
        params.append((a,packed_credits(x,r,l,a)))
    def best(n,d=None,close_pairs=None):
        rows=[evaluation(n,d,q,p,a,cs,close_pairs) for a,cs in params]
        rows=[v for v in rows if v is not None]
        return min(rows,key=lambda row:F(row['upper'])) if rows else None
    n=10600
    while F(best(n+1)['upper'])<1:
        n+=1
    out=best(n)
    next_out=best(n+1)
    assert F(out['upper'])<1<=F(next_out['upper'])
    test=11000
    lo,hi=0,200000
    assert F(best(test,lo)['upper'])<1
    while hi-lo>1:
        mid=(lo+hi)//2
        candidate=best(test,mid)
        if candidate is not None and F(candidate['upper'])<1:lo=mid
        else:hi=mid
    cond=best(test,lo)
    after=best(test,hi)
    assert F(cond['upper'])<1 and (after is None or F(after['upper'])>=1)
    near_pairs=[]
    for fixed_dups in [None,40000,80000,120000]:
        lo_pairs,hi_pairs=10000000,test*(test-1)//2+1
        while hi_pairs-lo_pairs>1:
            mid=(lo_pairs+hi_pairs)//2
            candidate=best(test,fixed_dups,mid)
            if candidate is not None and F(candidate['upper'])<1:lo_pairs=mid
            else:hi_pairs=mid
        row=best(test,fixed_dups,lo_pairs)
        assert row is not None and F(row['upper'])<1
        near_pairs.append(dict(max_parallel_pairs=fixed_dups,max_pairs_at_most_two=lo_pairs,
                               min_disk_population_on_failure=(2*(lo_pairs+1)+test-1)//test+1,
                               certificate=row))
    lim=evaluation(test,None,q,p,params[0][0],params[0][1])
    assert lim is not None
    barrier=unit_credit_limit(spec,test,q,p,lim['edge_ceiling'])
    assert F(barrier['aggregate_lower'])>F(10347,10000)
    return dict(profile=path.name,sha256=geo['sha256'],geometry_bins=geo['bins'],
                blank=str(q),edge_probability=str(p),diamond_r=str(r),diamond_l=str(l),
                universal=out,next_universal=next_out,
                conditional_max_parallel_pairs=lo,conditional=cond,
                next_conditional=after,unit_only_limit=barrier,close_pair_tests=near_pairs)

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
