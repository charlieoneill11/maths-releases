"""Near-neutral outward and antipodal sectors on regular ideal Parts B caps."""
import json
from fractions import Fraction as F
from ideal_area import D,Interval as I
from ideal_distance import add,sub,mul,dot,model,OPPOSITE

def lo(x):return F(x.lo,D)
def hi(x):return F(x.hi,D)

def check():
    x,H,_,v,edges,_=model()
    U=2*x
    assert OPPOSITE[4]==15
    O=mul(add(v[4],v[15]),I.num('.5'))
    R=I.num('.5')
    lower,upper=F('-.4985'),F('-.497')
    hmax=F('1e-8')
    def normal(t):
        t=I.num(t)
        return ((1-t*t).sqrt(),t)
    tips=[]
    for j in range(8):
        a,b=[normal(lower+(upper-lower)*i/8) for i in (j,j+1)]
        tang=mul(add(a,b),1/(1+dot(a,b)))
        for z in (a,b,tang):
            for r in (R,R+hmax):tips.append(add(O,mul(z,r)))
    left=min(lo(t[0]) for t in tips);right=max(hi(t[0]) for t in tips)
    bottom=min(lo(t[1]) for t in tips);top=max(hi(t[1]) for t in tips)
    n=v[5][1]
    assert 0<bottom<top<lo(n) and right<lo(U-v[9][0])
    # No other original tile is at this location. In the source's own tile
    # this height range sees only the exterior right arc 4.
    assert lo(U)>F('1.84') and hi(v[9][0])<1 and left>F('.86')
    assert max(q[0].hi for edge in edges for q,_ in edge)==v[9][0].hi
    assert hi(v[9][0])<F('.99')
    assert (right-left)**2+(top-bottom)**2<1 and hi(U)-lo(U)<F('.0000001')
    assert lo(U)-(right-left)>1 and F(3,2)-(top-bottom)>1
    # Any possible far-away same-color partner is strictly farther than 1.
    for m in range(-2,3):
        for k in range(-3,4):
            if (m,k)==(0,0):continue
            L=lo(U*m);S=hi(U*m)+F('.99')
            A=F(3*m,4)+F(3*k,2);B=A+F(1,2)
            assert max(0,left-S,L-right)**2+max(0,bottom-B,A-top)**2>1,(m,k)
    # The only edges above the top cut are 13, 14, 15. Their endpoints
    # on the cut are already in edges 12 and 16. The monotone arc hulls
    # add no vertex below the cut on these three edges.
    cut=v[13][1]
    for i in (13,14,15):
        assert all(q[1].lo>=cut.lo for q,_ in edges[i])
    for p in tips:
        for i,edge in enumerate(edges):
            if i in (13,14,15):continue
            for q,_ in edge:
                d=sub(p,q)
                assert dot(d,d).hi<D,(i,float(dot(d,d).hi/D))
    # Above the cut and to the right of the disk center all distances are
    # below 1. To its left the incident circular left wall bounds the tile
    # inside the radius-1/2 disk about O.
    assert max(right-lo(O[0]),F('.99')-left)**2+(F('.5')-bottom)**2<1
    # For delta, the deviation from the opposite radius, 1-cos(delta)<=4.01 h.
    # The chord inequality on [0,pi] gives first |delta|^2<=5(1-cos(delta)).
    # Once |delta|<.01, Taylor gives 1-cos(delta)>=.49 delta^2.
    assert (2+hmax)/(2*F('.5')*(F('.5')-hmax))<F('4.01')
    assert 5*F('4.01')*hmax<F('.01')**2 and F('4.01')/F('.49')<9
    # The expanded angular interval remains strictly inside the antipodal arc.
    # |sin(a)-sin(b)| <= |a-b|. Therefore normal ordinate gaps bound
    # angular distances from below.
    low_n=hi(2*(v[4][1]-O[1]));high_n=lo(2*(v[5][1]-O[1]))
    assert lower-low_n>F('.0003') and high_n-upper>F('.0003')
    widths={}
    for k in (8,10,12,14):
        h=F(1,10**k)
        ratio=1+6*F(1,10**(k//2))/(upper-lower)
        widths[str(h)]=dict(positive_fill_area_lower=str(F(1,2)*h*(upper-lower)),
                            erase_to_fill_upper=str(ratio),net_loss_to_fill_upper=str(ratio-1))
    return dict(normal_ordinates=[str(lower),str(upper)],max_radial_thickness=str(hmax),
                constructions=widths)

if __name__=='__main__':
    print(json.dumps(check(),indent=2))
