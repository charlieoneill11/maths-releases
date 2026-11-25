"""Certify the repaired windows, the previously erased cells, and free area.

Distances are tested on integer coordinates and rational interval bounds.
The free rectangles are interiors and each lies wholly in the starting
old color 2, the shared foreground erasure, and a certified new safe zone.
"""
from collections import Counter,defaultdict
from fractions import Fraction as F
from itertools import combinations
import json,math
from pathlib import Path
from cyclic_patch_check import G,Tiles,grid,inside_window,direction
from cyclic_patch_hex_check import rational
from ideal_distance import OPPOSITE,D,ideal_vertices,dot as idot,sub as isub
from verify import bbox,cross,distance_case,read_point,shifts
from exterior_exchange_search import distance_square

def rd(path):return json.loads(Path(path).read_text())
def center(w):return tuple(map(F,w['center']))
def coords(w):
    a,b=center(w);hw=F(w.get('width',w.get('side')))/2;hh=F(w.get('height',w.get('side')))/2
    return a-hw,a+hw,b-hh,b+hh
def outer(r):return tuple(f(d*G) for f,d in zip([math.floor,math.ceil]*2,r))
def inner(r):return tuple(f(d*G) for f,d in zip([math.ceil,math.floor]*2,r))
def sep(a,b):
    return max(0,a[0]-b[1],b[0]-a[1])**2+max(0,a[2]-b[3],b[2]-a[3])**2
def farthest(a,b):
    return max(abs(a[0]-b[1]),abs(a[1]-b[0]))**2+max(abs(a[2]-b[3]),abs(a[3]-b[2]))**2
def wholly_erased(b,Q):
    # For every p in B the minimum distance to the square Q is <1
    # and the maximum >1. Using an inscribed Q is conservative.
    X,x,Y,y=Q;v=[(a,c) for a in b[:2] for c in b[2:]]
    dmax=max(max(0,X-a,a-x)**2+max(0,Y-c,c-y)**2 for a,c in v)
    dx=x-X+max(0,X+x-2*b[1],2*b[0]-x-X)
    dy=y-Y+max(0,Y+y-2*b[3],2*b[2]-y-Y)
    return dmax<G*G and dx*dx+dy*dy>4*G*G

class Enclosure:
    def __init__(self,spec):
        self.tiles=Tiles(spec);self.s=spec;self.cache={}
        self.polys={p['color']:[tuple(map(grid,q)) for q in p['vertices']] for p in spec['pieces']}
        self.u,self.v=[[grid(t) for t in p] for p in spec['period']]
        self.boxes={c:bbox(p) for c,p in self.polys.items()}
        self.pad=10**8 # 1e-7 in physical units
        _,_,_,pts=ideal_vertices()
        assert max(idot(isub(pts[i],pts[i+1]),isub(pts[i],pts[i+1])).hi for i in OPPOSITE)*250**2<D
        assert (len(self.polys[1])-19)//8+1==64
        assert self.tiles.bounds['vertices']+5*self.tiles.bounds['period_x']<F('1e-11')
        # The .5-radius arc sagitta on a normalized 64th chord is <1e-8;
        # the parent interval proof is also in exterior_exchange_coverage.
        assert self.tiles.bounds['x_lo']>F('.9')
    def tile_two(self,b,tag):
        a,A,y,Y=b
        if not self.tiles.contains((a-10000,A+10000,y-10000,Y+10000),2):return False
        m,j=tag
        return a>m*self.u[0] and A<m*self.u[0]+G and y>m*self.u[1]+j*(G//2) and Y<m*self.u[1]+(j+1)*(G//2)
    def safe(self,b,c):
        q=[(b[0],b[2]),(b[1],b[2]),(b[1],b[3]),(b[0],b[3])]
        assert max(abs(t) for t in b)<4*G
        # Larger ideal columns cannot come within one even after the
        # inscribed-mesh and period uncertainties.
        for m,n,x,y in shifts(b,self.boxes[c],self.u,self.v,cross(self.u,self.v),G+self.pad):
            assert abs(m)<=5
            k=c,m,n
            if k not in self.cache:
                self.cache[k]=[(a+x,z+y) for a,z in self.polys[c]]
            p=self.cache[k]
            if distance_case(q,p,(G-self.pad)**2,False)=='near':continue
            # The old-2 containment check supplies disjoint interiors for
            # other colors. A closest boundary pair is vertex-to-edge.
            if distance_case(q,p,(G+self.pad)**2,False)=='far':continue
            return False
        return True
    def blank_near_axis(self,b):
        # Near x=0 only the unshifted horizontal column can touch the
        # box. Both orientations have the same left chain in |x|.
        from bisect import bisect_left,bisect_right
        assert max(abs(b[0]),abs(b[1]))<G//50
        assert max(abs(x) for x,y in self.tiles.p)<G and 2*self.tiles.bounds['x_lo']>F('1.8')
        chain=self.tiles.left;lim=max(abs(b[0]),abs(b[1]))+self.pad
        for j in range((b[2]-self.pad)//(G//2)-1,(b[3]+self.pad)//(G//2)+1):
            lo=max(chain.y[0],b[2]-j*(G//2)-self.pad);hi=min(chain.y[-1],b[3]-j*(G//2)+self.pad)
            if lo>hi:continue
            i=max(0,min(len(chain.xy)-2,bisect_right(chain.y,lo)-1))
            k=max(0,min(len(chain.xy)-2,bisect_left(chain.y,hi)-1))
            for y,n in [(lo,i),(hi,k)]:
                x0,y0=chain.xy[n];x1,y1=chain.xy[n+1]
                assert (x0-lim)*(y1-y0)+(x1-x0)*(y-y0)>0
            assert all(x>lim for x in chain.x[bisect_left(chain.y,lo):bisect_right(chain.y,hi)])
        return True

    def fg_ok(self,fg):
        S,T,Q=[center(q) for q in fg];u=tuple(q-t for q,t in zip(Q,S));v=tuple(q-t for q,t in zip(Q,T))
        assert all(sum(s*s for s in w)==1 for w in (u,v))
        assert [p['color'] for p in fg]==[1,1,2] and [p['old'] for p in fg]==[0,0,1]
        assert F(fg[0]['side'])==F(fg[1]['side']) and F(fg[2]['side'])<=F(fg[0]['side'])
        for w in fg[:2]:
            b=outer(coords(w));seen=set()
            for k in range(0,32768,4):
                v=direction(k)
                for c in set(range(1,7))-seen:
                    if inside_window(self.tiles,b,v,c):seen.add(c)
                if len(seen)==6:break
            assert len(seen)==6
        b=outer(coords(fg[2]));assert self.tiles.contains((b[0]-10000,b[1]+10000,b[2]-10000,b[3]+10000),1)
        for i,j in combinations(range(3),2):
            a,b=[tuple(F(t) for t in coords(fg[k])) for k in [i,j]]
            assert sep(a,b)>0
            if fg[i]['color']==fg[j]['color']:assert sep(a,b)>=1 or farthest(a,b)<=1

def verify(spec,rec):
    chk=Enclosure(spec);fg=rec['foreground'];chk.fg_ok(fg)
    spec_rects=[coords(w) for w in fg];q=inner(coords(fg[2]));stacks=defaultdict(list);area=Counter();old_area=Counter()
    sources=[outer(coords(w)) for w in fg[:2]]
    for w in rec.get('paid',[]):
        r=coords(w);B=outer(r);tag=tuple(w['tile']);assert chk.tile_two(B,tag) and wholly_erased(B,q)
        assert w['color'] in [1,3,4,5,6]
        if w['color']==1:assert all(sep(B,r)>G**2 or farthest(B,r)<G**2 for r in sources)
        spec_rects.append(r);old_area[tag]+=F(w['side'])**2
    for rec0 in rec.get('free',[]):
        c=rec0['color'];tag=tuple(rec0['tile']);assert c in [1,3,4,5,6]
        for raw in rec0['boxes']:
            B=tuple(raw);assert all(type(t) is int for t in B) and B[0]<B[1] and B[2]<B[3]
            assert chk.tile_two(B,tag) and wholly_erased(B,q) and chk.safe(B,c)
            if c==1:assert all(sep(B,r)>G**2 or farthest(B,r)<G**2 for r in sources)
            stacks[tag].append(B);area[tag]+=F((B[1]-B[0])*(B[3]-B[2]),G**2)
    def overlap(a,b):return a[0]<b[1] and b[0]<a[1] and a[2]<b[3] and b[2]<a[3]
    for b in spec_rects:
        assert max(abs(b[0]),abs(b[1]))+2<10*chk.tiles.bounds['x_lo'] and max(abs(b[2]),abs(b[3]))+2<6
    all_windows=[(outer(r),None) for r in spec_rects]+[(b,tag) for tag,boxes in stacks.items() for b in boxes]
    ordered=sorted(all_windows,key=lambda r:r[0][2])
    for i,(b,tag) in enumerate(ordered):
        assert max(abs(b[0]),abs(b[1]))+2*G<10*chk.tiles.bounds['x_lo']*G and max(abs(b[2]),abs(b[3]))+2*G<6*G
        for d,_ in ordered[i+1:]:
            if d[2]>=b[3]:break
            assert not overlap(b,d)
    # All free and paid satellites were originally 2: any pair of their
    # points avoids unit distance, regardless of their new labels.
    return dict(source_area=str(sum(F(w['side'])**2 for w in fg[:2])),
        free_boxes=sum(map(len,stacks.values())),free_area_by_tile={str(k):str(a) for k,a in area.items()},
        exact_free_recovery=str(sum(area.values())),free_recovery_float=float(sum(area.values())),
        paid_recovery=str(sum(old_area.values())),active_tiles=sorted([list(k) for k in set(area)|set(old_area)]))
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',nargs='?',default='distributed_patch.json');a=p.parse_args()
    print(json.dumps(verify(rd('parts64.json'),rd(a.input)),indent=2))
