"""Combine monochromatic-edge and double-hole-hit bounds for a polygon defect coloring.

The caller certifies b, p and the indicated diamond within the blank area.
The diamond centers form a lattice of cell area 2xy, with vertical period y.
The graph edge ceiling is the published Ágoston–Pálvölgyi unit-distance bound.
"""
import argparse
from fractions import Fraction as F
from math import ceil,isqrt
import json


def pos(v):return max(0,v)


def diamond_credits(x,y,r,l,half,steps=256):
    density=r*l/(x*y)
    def cov(dx,dy):
        # Transform the diamond to [-1,1]^2. The overlap decreases with
        # either absolute coordinate in the physical (x,y) frame by slices.
        u,v=dx/r,dy/l
        return density*pos(1-(u+v)/2)*pos(1-abs(u-v)/2)
    theta2pi=F(7,11)
    aligned=F(0)
    for j in range(1,steps+1):
        t=half*j/steps
        aligned+=cov(t,abs(1-2*y)+t*t/2)
    aligned*=half*theta2pi/steps
    near=F(0);cut=2*half
    for j in range(157):
        a=F(j,100); b=a+F(1,100)
        X=cut*(1-a*a/2+a**4/24-a**6/720+a**8/40320)
        Y=cut*(b-b**3/6+b**5/120-b**7/5040+b**9/362880)
        near+=cov(X,Y)
    near*=theta2pi/100
    return near,aligned


def edge_ceiling(n):
    # Unit distances <= (29/4)^(1/3) * n^(4/3).
    # Find the floor by exact cubing.
    lo,hi=0,n*(n-1)//2+1
    while lo+1<hi:
        mid=(lo+hi)//2
        if 4*mid**3<=29*n**4:lo=mid
        else:hi=mid
    return lo


def cross_upper(k,s,L):
    bounds=[s*L,k*s,k+s*(s-1)]
    for a,b in [(s,k),(k,s)]:
        j0=isqrt(2*a*(a-1)//max(b,1))
        for j in range(max(1,j0-1),max(2,j0+3)):
            bounds.append(((j+1)*b*j+2*a*(a-1))//(2*j))
    return min(bounds)


def combine(n,blank,defect,half,near,aligned,mode='both'):
    m=edge_ceiling(n)
    # At fixed s, increasing the actual edge count increases the expected
    # defect term by defect per edge. The savings below have Lipschitz
    # constant aligned in that edge count. Thus the endpoint m is worst.
    assert defect>=aligned
    L=ceil(F(44,7)/(2*half))-1
    minimum=None
    for s in range(n+1):
        if minimum is not None and s*near>=minimum:break
        k=n-s
        D=cross_upper(k,s,L)
        I=min(s*(s-1)//2,(s+isqrt(s*s*max(0,8*s-7)))//4)
        edges=max(0,m-D-I)
        close_pairs=s*(s-1)//2+5*s
        credit=s*near+edges*aligned
        if mode=='both':credit=max(credit,(m-close_pairs)*aligned)
        if minimum is None or credit<minimum:
            minimum, index, retained=credit,s,edges
    E=n*blank+m*defect-minimum
    return {'order':n,'max_edges':m,'blank_upper':str(blank),'defect_upper':str(defect),
            'close_credit':str(near),'aligned_credit':str(aligned),
            'worst_discards':index,'rep_edges':retained,'forest_discount':float(minimum),
            'expected_upper':str(E),'expected_decimal':float(E),'certified':E<1}


if __name__=='__main__':
    q=argparse.ArgumentParser(description=__doc__)
    for name in ('x','y','r','l','blank','defect'):
        q.add_argument('--'+name,type=F,required=True)
    q.add_argument('--order',type=int,default=10000)
    q.add_argument('--angle',type=int,nargs='*',default=[20,24,28,30,32,34,36,38])
    a=q.parse_args()
    for j in a.angle:
        half=F(j,10000)
        c,b=diamond_credits(a.x,a.y,a.r,a.l,half)
        r=combine(a.order,a.blank,a.defect,half,c,b)
        print(json.dumps(dict(angle=str(half),**r)),flush=True)
