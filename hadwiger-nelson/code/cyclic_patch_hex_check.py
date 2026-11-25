"""Independently verify the rational two-hole six-cycle patch and its collar."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
from cyclic_patch_check import Tiles, G, N as NANG, direction, inside_window
from exterior_exchange_search import distance_square

SIDE=F(1,250)
t=F(12701665,10**8)
W=((1-t*t)/(1+t*t),2*t/(1+t*t))
def rational(k):
    i,j=divmod(k,NANG//4);t=F(j,NANG//4)
    x,y=(1-t*t)/(1+t*t),2*t/(1+t*t)
    return ((x,y),(-y,x),(-x,-y),(y,-x))[i]

def template(turns):
    add=lambda p,q:tuple(x+y for x,y in zip(p,q))
    a,b,c=map(rational,turns)
    S=[(F(0),F(0)),(F(0),2*W[1])]
    P=[W,add(W,a),add(add(W,a),b),add(add(add(W,a),b),c),add(add(W,b),c),add(W,c)]
    return S+P

def check(spec,rec):
    pts=template(rec['turns']);labs=rec['old_hexagon'];assert sorted(labs)==list(range(1,7))
    assert [W, (W[0],-W[1])]==[tuple(z-p for z,p in zip(pts[2],q)) for q in pts[:2]]
    norm=lambda p:sum(x*x for x in p)
    assert norm(W)==1
    for a,b in zip(pts[2:],pts[3:]+[pts[2]]):assert norm([u-v for u,v in zip(a,b)])==1
    assert pts==[tuple(map(F,p)) for p in rec['centers']] and SIDE==F(rec['side'])
    assert rec['labels']==[labs[0],labs[0]]+labs[1:]+labs[:1]
    tile=Tiles(spec);scale=lambda s:s*G
    import math
    source_steps=[]
    for i,(x,y) in enumerate(pts):
        if i<2:
            # Both are in the signed copies of the first two previously
            # certified blank staircase bands (relative to one A center).
            yy=y-(F(1,2) if i else 0)
            assert abs(x)+SIDE/2<F('.0031') and abs(yy)+SIDE/2<F('.004')
            # Verify blankness directly by finding one unit-translated
            # copy of the entire square strictly inside each old color.
            q=(math.floor((x-SIDE/2)*G),math.ceil((x+SIDE/2)*G),
               math.floor((y-SIDE/2)*G),math.ceil((y+SIDE/2)*G))
            seen={}
            for code in range(0,NANG,4):
                v=direction(code)
                for col in set(range(1,7))-set(seen):
                    if inside_window(tile,q,v,col):seen[col]=code
                if len(seen)==6:break
            assert len(seen)==6
            source_steps.append([seen[col] for col in range(1,7)])
        else:
            q=[math.floor(scale(x-SIDE/2))-10000,math.ceil(scale(x+SIDE/2))+10000,
               math.floor(scale(y-SIDE/2))-10000,math.ceil(scale(y+SIDE/2))+10000]
            assert tile.contains(tuple(q),labs[i-2])
    for i,j in combinations(range(8),2):
        assert any(abs(u-v)>SIDE for u,v in zip(pts[i],pts[j]))
        if rec['labels'][i]==rec['labels'][j]:
            lo,hi=distance_square(pts[i],pts[j],SIDE);assert hi<=1 or lo>=1
    # All changes, including unit erasures, are separated from the block edge by one.
    assert all(abs(x)+SIDE/2+2<10*tile.bounds['x_lo'] and abs(y)+SIDE/2+2<6 for x,y in pts)
    return {'jointly_filled':str(2*SIDE*SIDE),'cycle_cell_area':str(SIDE*SIDE),'old_hexagon':labs,'new_labels':rec['labels'],'old_color_witness_turns_at_both_sources':source_steps}

if __name__=='__main__':
    read=lambda name:json.loads(Path(name).read_text())
    print(json.dumps(check(read('parts64.json'),read('cyclic_patch_hexagon.json')), indent=2))
