"""Two A sectors and a B sector with the whole old color 4 free to change."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json

from cyclic_patch_check import G,Tiles,inside_window,direction
from distributed_patch_check import outer
from ideal_area import D, Interval as I
from ideal_distance import ideal_vertices,add,mul,sub,dot
from push4_shape_sector import check as certify_sectors_b
from push4_shape_sector_a import check as certify_sectors_a

ROOT=Path(__file__).resolve().parent
HMAX=F(1,10**8)
SOURCE=('Ltop','Llow','Rlow')
DONOR=('Rlow','Rtop','Ltop')


def grow(q,margin):
    x,X,y,Y=q
    return (x-margin,X+margin,y-margin,Y+margin)


def flip(q):
    return (*q[:2],G//2-q[3],G//2-q[2])


def gap(q,b):
    return max(q[0]-b[1],b[0]-q[1],q[2]-b[3],b[2]-q[3])


def shifted(q,v):
    return (q[0]+v[0].lo*G//D,q[1]-((-v[0].hi)*G//D),
            q[2]+v[1].lo*G//D,q[3]-((-v[1].hi)*G//D))


def run():
    certify_sectors_a()
    certify_sectors_b()
    tiles=Tiles(json.loads((ROOT/'parts64.json').read_text()))
    record=json.loads((ROOT/'joint6_mask_rays.json').read_text())
    x,H,_,v=ideal_vertices()
    O=mul(add(v[4],v[15]),F(1,2))
    R=I.num('.5')
    h=I.num(HMAX)
    n=I(I.num('-.4988').lo,I.num('-.4967').hi)
    shells=I((R-h).lo,R.hi)
    charts={}
    for tag,sign in [('Ltop',-1),('Rlow',1)]:
        X=O[0]+sign*shells*(1-n*n).sqrt()
        Y=O[1]+sign*shells*n
        charts[tag]=grow(outer(tuple(F(z,D) for z in (X.lo,X.hi,Y.lo,Y.hi))),10**8)
    charts['Llow']=flip(charts['Ltop'])
    charts['Rtop']=flip(charts['Rlow'])
    assert len(DONOR)==len(set(DONOR))==3
    assert all(gap(q,b)>0 for q,b in combinations(charts.values(),2))

    # The source and its unit-matched receiver fall in the respective
    # opposite charts. Compare with the radius R point at the same normal
    # ordinate. Let r>=R, X=r*sqrt(1-t^2), Z=sqrt(R^2-r^2*t^2). The
    # matched abscissa relative to its center is +/- (X-2Z).
    # 2|X-Z|=2(r^2-R^2)/(X+Z), and each change in Y is at most h.
    r=I(R.lo,(R+h).hi)
    t=I(I.num('-.4985').lo,I.num('-.497').hi)
    X=r*(1-t*t).sqrt()
    Z=(R*R-r*r*t*t).sqrt()
    assert (X+Z).lo>F('.8')*D
    assert HMAX + 2*HMAX*(1+HMAX)/F('.8') < F(1,10**7)
    assert O[1].lo==O[1].hi==D//4
    assert charts['Ltop'][0]>0 and charts['Ltop'][1]<G//100
    assert charts['Rlow'][0]>8*G//10 and charts['Rlow'][1]<9*G//10
    for tag in ('Ltop','Rlow'):
        a,b=charts[tag][2:]
        if tag=='Ltop':
            assert v[16][1].hi*G<a*D and b<G//2
        else:
            assert 0<a and b*D<v[5][1].lo*G
    # Standard superperiod (10U,0),(0,12). Every support or unit guard
    # checked here is in [-3,3]^2 and cannot run into another block.
    assert 20*x.lo>18*D

    direct=0
    fixed={2,3,5,6}
    for tag,q in charts.items():
        ds={int(c):k for c,k in record['direct'][tag].items()}
        assert set(ds)==fixed
        for c,k in ds.items():
            assert inside_window(tiles,q,direction(k),c)
            direct+=1
    guard=[]
    for expected,(tag,k,rays) in zip(SOURCE+DONOR,record['charges'],strict=True):
        assert tag==expected
        v=direction(k)
        assert inside_window(tiles,charts[tag],v,4)
        b=shifted(charts[tag],v)
        assert all(gap(b,other)>0 for other in guard)
        guard.append(b)
        assert {int(c) for c in rays}==fixed|{1}
        for c_string,code in rays.items():
            c=int(c_string); step=direction(code)
            assert inside_window(tiles,b,step,c)
            z=shifted(b,step)
            assert max(abs(a) for a in z)<3*G
            if c==1:
                assert all(gap(z,charts[t])>0 for t in DONOR)
    # An actual shared old4 patch from both A-sector donors. The transverse
    # radii h/16 stay inside each forced old1 erasure. An antipodal source at
    # radius 1-s is in the A sector since its normal ordinate is close to t.
    t=I.num('-.4982'); radial=R-h/2
    p=add(O,mul(((1-t*t).sqrt(),t),radial))
    d=I.num('.25')-p[1]
    common=(p[0]-(1-d*d).sqrt(),I.num('.25'))
    q=outer([F(z,D) for z in (common[0].lo,common[0].hi,common[1].lo,common[1].hi)])
    assert tiles.contains(grow(q,G//10000+10000),4)
    assert F(2)*HMAX/16/(F('.5')-HMAX) < F('.0001')
    guard_gap=F(min(gap(a,b) for a,b in combinations(guard,2)),G)
    return dict(sources=list(SOURCE),donors=list(DONOR),charts_1e15=charts,
                disjoint_old4_boxes_1e15=guard,
                min_disjoint_old4_gap_in_coordinate=str(guard_gap),direct_fixed_rays=direct,
                second_layer_rays=30,common_old4_center_box_1e15=q,
                common_old4_disk_radius_at_h_1e_minus_8=str(HMAX/16),
                common_disk_area_over_pi=str((HMAX/16)**2),
                repeat='(10U,0),(0,12), U=2x',net_area_gain_upper=0,
                old_color4_may_change_everywhere=True)


if __name__=='__main__':
    print(json.dumps(run(),indent=2))
