"""Area control for a feasible simultaneous two-A-plus-B repair with two switches."""
from fractions import Fraction as F
from pathlib import Path
from math import ceil,floor
import json

from cyclic_patch_check import G,Tiles,direction
from distributed_patch_check import outer
from ideal_area import D,Interval as I,arcsin
from ideal_distance import ideal_vertices,add,mul
from joint6_mask import ROOT,grow

H=F('1e-8')
DISK=H/16
PI_LO,PI_HI=F('3.1415926'),F('3.1415927')


def verify_pi():
    # Alternating arctangent series in Machin's identity.
    def arctan(x,n):
        total=sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(n))
        next_term=(-1)**n*x**(2*n+1)/(2*n+1)
        return sorted((total,total+next_term))
    l,h=arctan(F(1,5),10)
    a,b=arctan(F(1,239),4)
    assert PI_LO<16*l-4*b<16*h-4*a<PI_HI


def bounds(l,h):
    scale=10**24
    def dec(i):
        a,b=divmod(abs(i),scale)
        return ('-' if i<0 else '')+f'{a}.{b:024d}'
    return [dec(floor(l*scale)),dec(ceil(h*scale))]


def ring(tiles,center):
    # Each quadrant uses t in [0,1] with angle derivative 2/(1+t^2).
    # At every t subdivision both coordinates are monotone. Allow the
    # entire radial thickness and the uncertainty of the center coordinates.
    bins=2048;step=8192//bins
    lower=upper=F(0); uncertain_bins=old4_bins=0
    for i in range(4*bins):
        a=direction(i*step);b=direction(((i+1)*step)%32768)
        limits=[]
        for z,p,q in zip(center,a,b):
            unit=I(min(p.lo,q.lo),max(p.hi,q.hi))
            coord=z+unit*I(I.num(1-DISK).lo,I.num(1+DISK).hi)
            limits.extend([F(coord.lo,D),F(coord.hi,D)])
        box=grow(outer(limits),10000)
        t=i%bins
        dl=F(2*bins,bins*bins+(t+1)**2)
        dh=F(2*bins,bins*bins+t*t)
        if tiles.contains(box,4):
            lower+=dl;upper+=dh;old4_bins+=1
        elif not any(tiles.contains(box,c) for c in (1,2,3,5,6)):
            upper+=dh;uncertain_bins+=1
    return 2*DISK*lower,2*DISK*upper,old4_bins,uncertain_bins


def run():
    verify_pi()
    tiles=Tiles(json.loads((ROOT/'parts64.json').read_text()))
    x,height,_,v=ideal_vertices()
    O=mul(add(v[4],v[15]),F(1,2))
    R=I.num('.5')
    L_A=arcsin(I.num('.4985'))-arcsin(I.num('.4979'))
    L_B=arcsin(I.num('.4974'))-arcsin(I.num('.497'))
    length=2*L_A+L_B
    # Between the upper A source and the B source, the absolute angular
    # difference is at least .0005. Chord-squared = (r+s)^2-2rs(1-cos d).
    # On the entire short angle range, 1-cos(d) >= .49*d^2.
    assert (1+2*H)**2-2*F('.5')**2*F('.49')*F('.0005')**2<1
    fills=I.num(H)*(R+I.num(H/2))*length
    old1_delta=I.num(18*H*F('.0001'))*(R-I.num(H/2))-I.num(H*H)*length
    t=I.num('-.4982')
    p=add(O,mul(((1-t*t).sqrt(),t),R-I.num(H/2)))
    Z=[p,(p[0],height-p[1])]
    separation=height-2*p[1]
    assert separation.lo>F('.495')*D
    # Normals of the switched subdisks vary by less than 2*disk/(R-h).
    # Their radii are in (R-9h/16,R-7h/16), so the exact antipodal unit
    # mates lie strictly inside the occupied A interval and radial range.
    assert 2*DISK/(F('.5')-H)<F('.0001')
    d=I.num('.25')-p[1]
    q=p[0]-(1-d*d).sqrt(),I.num('.25')
    B=outer([F(z,D) for z in (q[0].lo,q[0].hi,q[1].lo,q[1].hi)])
    assert tiles.contains(grow(B,G//12+10000),4)
    costs=[ring(tiles,center) for center in Z]
    # For a common shadow point, difference of squared distances to Z's is
    # 2*separation*(y-1/4), giving |y-1/4|<=2*disk/separation. Only two
    # horizontal radial bands occur. Each has width <=4*disk/1.9, since
    # its sqrt endpoints share a sum >1.9.
    assert F('.25')+2*DISK/F('.495')<F('.251')
    assert 4*((1-DISK)**2-F('.251')**2)>F('1.9')**2
    assert F(4)/F('.495')*2*4/F('1.9')<35
    sl,sh=PI_LO*DISK**2,35*DISK**2
    joint=(sum(c[0] for c in costs)-sh,sum(c[1] for c in costs)-sl)
    loss=(F(old1_delta.lo,D)+joint[0]-2*PI_HI*DISK**2,
          F(old1_delta.hi,D)+joint[1]-2*PI_LO*DISK**2)
    assert loss[0]>0 and sl>0
    return dict(h=str(H), switch_disk_radius=str(DISK),
                A_source_ordinate=['-.4985','-.4979'], B_source_ordinate=['-.4974','-.497'],
                occupied_area=bounds(F(fills.lo,D),F(fills.hi,D)),
                old1_blanket_erase_minus_original_fill=bounds(F(old1_delta.lo,D),F(old1_delta.hi,D)),
                old4_erasure_if_switched_separately=[bounds(a,b) for a,b,_,_ in costs],
                angular_bins_old4_and_uncertain=[[c,d] for a,b,c,d in costs],
                common_old4_erasure=bounds(sl,sh),joint_old4_erasure=bounds(*joint),
                switches_restored_to_4=bounds(2*PI_LO*DISK**2,2*PI_HI*DISK**2),
                net_increase_in_blank_area=bounds(*loss))


if __name__=='__main__':
    print(json.dumps(run(),indent=2))
