"""Exact checks of cyclic palette-switch paths. No numerical search imports."""
from bisect import bisect_left, bisect_right
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations
import argparse
import json
from pathlib import Path
from ideal_area import D, Interval as I
from ideal_distance import add, sub, mul, dot
from ideal_proxy import check as proxy_check

G=10**15
N=32768

@lru_cache(None)
def direction(k):
    assert type(k) is int and 0<=k<N
    q,r=divmod(k,N//4)
    t=F(r,N//4); x,y=(1-t*t)/(1+t*t),2*t/(1+t*t)
    ab=[(x,y),(-y,x),(-x,-y),(y,-x)][q]
    return tuple(map(I.num,ab))

@lru_cache(None)
def follow(turns):
    if not turns:return ((I.num(0),I.num(0)),)
    path=follow(turns[:-1])
    return path+(add(path[-1],direction(turns[-1])),)

def walk(path):
    left,right,sign=path
    assert sign in (-1,1) and left and right
    a,b=follow(tuple(left))[1:],follow(tuple(right))[1:]
    d=sub(b[-1],a[-1]);width=dot(d,d)
    assert 0<width.lo and width.hi<4*D
    alt=(1/width-I.num('0.25')).sqrt()*sign
    mid=add(mul(add(a[-1],b[-1]),I.num('.5')),mul((-d[1],d[0]),alt))
    return a+(mid,)+b[::-1]

def grid(t):
    n=F(t)*G
    assert n.denominator==1
    return n.numerator

class Chain:
    def __init__(self,points):
        self.xy=sorted(points,key=lambda p:p[1])
        self.y=[y for x,y in self.xy]
        self.x=[x for x,y in self.xy]
        assert all(a<b for a,b in zip(self.y,self.y[1:]))
    def inside(self,lo,hi,edge,sg):
        i=bisect_right(self.y,lo)-1;j=bisect_left(self.y,hi)
        if i<0 or j>=len(self.y):return False
        def test(y,k):
            x0,y0=self.xy[k];x1,y1=self.xy[k+1]
            return sg*((edge-x0)*(y1-y0)-(x1-x0)*(y-y0))>0
        if not test(lo,i) or not test(hi,j-1):return False
        return all(sg*(edge-x)>0 for x in self.x[i+1:j])

class Tiles:
    def __init__(self,spec):
        self.bounds=proxy_check(spec)
        assert self.bounds['vertices']+5*self.bounds['period_x']<F('1e-11')
        self.ux,self.uy=map(grid,spec['period'][0])
        assert self.uy==3*G//4 and tuple(map(grid,spec['period'][1]))==(0,3*G//2)
        self.p=[tuple(map(grid,pt)) for pt in spec['pieces'][0]['vertices']]
        self.left=Chain([p for p in self.p if p[0]<G//2])
        self.right=Chain([p for p in self.p if p[0]>=G//2])
        cycle=self.left.xy[::-1]+self.right.xy
        start=cycle.index(self.p[0])
        assert cycle[start:]+cycle[:start]==self.p
        assert self.left.y[0]==self.right.y[0] and self.left.y[-1]==self.right.y[-1]
        assert self.left.y[0]>0 and self.left.y[-1]<G//2
        assert spec['pieces'][0]['color']==1
        for k,raw in enumerate(spec['pieces']):
            assert raw['color']==[1,3,2,4,6,5][k]
            assert [tuple(map(grid,p)) for p in raw['vertices']]==[
                ((1 if k<3 else -1)*x,y+(k%3)*G//2) for x,y in self.p]
    @lru_cache(None)
    def contains(self,coords,color):
        x,X,y,Y=coords
        for m in [x//self.ux,x//self.ux+1]:
            if abs(m)>5:continue
            a,b=x-m*self.ux,X-m*self.ux
            if a>=0:h=0
            elif b<=0:h=1;a,b=-b,-a
            else:continue
            lo,hi=y-m*self.uy,Y-m*self.uy;j=lo//(G//2)
            if color!=1+3*h+(-j)%3:continue
            lo-=j*(G//2);hi-=j*(G//2)
            if not self.left.y[0]<lo<=hi<self.left.y[-1]:continue
            if self.left.inside(lo,hi,a,1) and self.right.inside(lo,hi,b,-1):return True
        return False

def inside_window(tiles,q,offset,c):
    pad=10000
    a,b=offset
    def fl(v):return v*G//D
    def ce(v):return -( (-v*G)//D )
    X=(q[0]+fl(a.lo)-pad,q[1]+ce(a.hi)+pad,q[2]+fl(b.lo)-pad,q[3]+ce(b.hi)+pad)
    return tiles.contains(X,c)


def check(spec,data,allow_missing):
    tiles=Tiles(spec)
    regions=[];total=0;counts=Counter();missing=[];bad=[];longest=0
    # A compact integer outward enclosure with an extra 10^-11 margin
    # compared with the exact square root and ideal inscribed broken lines.
    allseq={s for k in [3,4,5,6] for s in permutations(range(1,7),k) if s[0]<s[-1]}
    def overlap(a,b):return max(a[0],b[0])<min(a[1],b[1]) and max(a[2],b[2])<min(a[3],b[3])
    for idx,row in enumerate(data):
        q=tuple(map(grid,row['box']))
        assert 0<=q[0]<q[1]<G//10 and 0<=q[2]<q[3]<G//10
        assert not any(overlap(q,b) for b in regions)
        regions.append(q)
        solved=set()
        for s,r,path in row['paths']:
            seq=tuple(s);key=(idx,seq)
            assert seq in allseq and seq not in solved and r>0
            vs=walk(path);assert len(vs)==len(seq)*r
            if all(inside_window(tiles,q,v,c) for v,c in zip(vs,seq*r)):
                solved.add(seq);counts[(len(s),r)]+=1;longest=max(longest,len(vs)+1)
            else:bad.append(key)
        missing.extend([(idx,k) for k in sorted(allseq-solved)])
        total+=(q[1]-q[0])*(q[3]-q[2])
    # For the ideal model the symmetries in ideal_distance.vertices_from_parameters
    # are exact. For the rational proxy compare the reflected polygon with
    # the original. Corresponding vertices are at most 2 grid units apart,
    # so every reflected certified box still lies inside its reflected tile.
    refl=[(x,G//2-y) for x,y in tiles.p][::-1]
    i=min(range(len(refl)),key=lambda i:max(abs(x-z) for x,z in zip(refl[i],tiles.p[0])))
    refl=refl[i:]+refl[:i]
    assert max(abs(x-z) for a,b in zip(refl,tiles.p) for x,z in zip(a,b))<100
    # Reflection in x swaps the two orientations, and translating by one
    # half-row permutes each triple of labels cyclically. Conjugation by
    # any global permutation preserves the family being tested.
    lower=F(12*total,G**2)/(3*tiles.bounds['x_hi'])
    if not allow_missing:assert not missing and not bad
    return dict(checked=len(data),unoriented_paths=sum(counts.values()),invalid=bad,
                missing=missing,longest_closed_walk=longest,by_length={str(k):v for k,v in sorted(counts.items())},
                combined_with_singletons_and_pairs_lower=float(lower),
                exact_lower=str(lower),meets_threshold=not missing and lower>F(1,10000))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--allow-missing',action='store_true')
    parser.add_argument('--single',type=int)
    args=parser.parse_args()
    rd=lambda p:json.loads(Path(p).read_text())
    data=[rd(f'cyclic_patch_{i}.json') for i in ([args.single] if args.single is not None else range(6))]
    ref=rd('kempe_cycles.json')['patches']
    which=[args.single] if args.single is not None else range(6)
    assert all(r['box']==ref[k]['box'] for k,r in zip(which,data))
    result=check(rd('parts64.json'),data,args.allow_missing)
    print(json.dumps(result,indent=2))
