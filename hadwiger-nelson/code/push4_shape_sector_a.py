"""Certify a near-neutral sector of the A hole on the radius-one-half arc 15."""
from fractions import Fraction as F
from itertools import product
import json
from ideal_area import D,Interval as I
from ideal_distance import add,sub,mul,dot,model,OPPOSITE

def lo(t):return F(t.lo,D)
def hi(t):return F(t.hi,D)

def check():
    x,H,_,v,edges,_=model();U=2*x;R=I.num('.5');O=mul(add(v[4],v[15]),R)
    assert OPPOSITE[4]==15 and OPPOSITE[15]==4 and O[1].lo==O[1].hi==D//4
    lower,upper=F('-.4985'),F('-.497');h=F('1e-8')
    def unit(t):
        t=I.num(t);return ((1-t*t).sqrt(),t)
    tips=[]
    for k in range(8):
        a,b=[unit(lower+(upper-lower)*i/8) for i in [k,k+1]]
        # The triangle formed by the endpoints and intersecting tangents
        # contains the circular arc. Use its opposite directions on the A side.
        tangent=mul(add(a,b),1/(1+dot(a,b)))
        for w,r in product((a,b,tangent),(R,R+h)):tips.append(sub(O,mul(w,r)))
    left,right=min(lo(t[0]) for t in tips),max(hi(t[0]) for t in tips)
    low,top=min(lo(t[1]) for t in tips),max(hi(t[1]) for t in tips)
    assert 0<left<right<lo(O[0]) and hi(v[16][1])<low<top<lo(v[15][1])
    assert all(0<=q[0].lo<=q[0].hi<D for e in edges for q,_ in e)
    assert lo(U)>F('1.84') and lo(U)-1>right
    # Own left boundary at these heights is the left branch of arc 15.
    # r>R puts the source outside the disk. Its x>0 excludes the opposing
    # reflected half-tile; other columns and vertical rows also miss it.
    assert (right-left)**2+(top-low)**2<1 and lo(U)-(right-left)>1 and F(3,2)-(top-low)>1
    assert (left+2*lo(O[0])-2*max(hi(v[i][0]) for i in [15,16]))>F('.85')
    assert max(hi(p[0]) for j in [0,1,2,15,16,17,18] for p,_ in edges[j])<F('.01')
    # Orthogonal coordinate monotonicity of this small minor arc bounds L(y)
    # between its endpoints. Its antipode gives the original right wall at
    # reflected height. The horizontal fiber translation lands inside that wall.
    assert 0<F('.5')-top<F('.5')-low<lo(v[5][1])
    # All of the own tile except the circular segment between arc 4 and
    # its chord is enclosed by the convex hull of the other boundary pieces.
    far2=max(dot(sub(p,q),sub(p,q)).hi for p in tips for i,e in enumerate(edges) if i!=4 for q,_ in e)
    assert far2<I.num('.9999993').lo
    # All distant tiles whose coarse rectangles might approach one.
    near=(-1,1)
    for m,n in product(range(-1,2),repeat=2):
        if (m,n) in [(0,0),near]:continue
        i,j=sorted((m*lo(U),m*hi(U)));a=F(3*m,4)+F(3*n,2)
        assert max(0,i-right,left-j-1)**2+max(0,a-top,low-a-F('.5'))**2>1
    # |m|>=2 or (|m|<=1 and |n|>=2) exceed one by an axis gap.
    assert 2*lo(U)-1-right>1 and F(3)-F(3,4)-F('.5')-top>1
    axes=[(-990,140),(-991,137),(-991,135),(-968,249),(-968,253),(-942,336),(-924319,381620),
          (-909,416),(-870,493),(-868,496),(-867,498),(-841,541),(-817,576),(-794,608),
          (-793,609),(-926,378),(-927,376),(-929,371),(-990,142)]
    offset=(-U,I.num('.75')); bound=F('1.000265')
    for e,(a,b) in zip(edges,axes,strict=True):
        axis=(I.num(a),I.num(b))
        gap=min(dot(add(q,offset),axis).lo for q,_ in e)-max(dot(p,axis).hi for p in tips)
        assert gap>0 and gap*gap>bound*bound*D*D*(a*a+b*b)
    # Inside the cap disk, a unit contact must be within h radially and
    # 3 sqrt(h) in angle of the antipode. Both endpoint extensions fit arc 4.
    assert lower-hi(2*(v[4][1]-O[1]))>F('.0003') and lo(2*(v[5][1]-O[1]))-upper>F('.0003')
    assert (2+h)/(2*F('.5')*(F('.5')-h))<F('4.01')
    assert 5*F('4.01')*h<F('.01')**2 and F('4.01')/F('.49')<9
    return dict(positive_inward_normal_y=list(map(str,(lower,upper))),max_h=str(h),
                critical_skew=[-1,1],skew_boundary_distance_lower=str(bound),
                own_chorded_tile_distance_sq_upper=str(F(far2,D)),
                fill_area_lower='0.00075*h',erasure_to_fill_lower='1',
                erasure_to_fill_upper='1+4000*sqrt(h)')
if __name__=='__main__':print(json.dumps(check(),indent=2))
