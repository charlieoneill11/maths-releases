"""Exact six-label test for joint A/B fills with mutable annuli of old colors.

Usage: python adaptive_recolor.py --search   to regenerate the witness graph
       python adaptive_recolor.py            to check using standard-library arithmetic

New coverage is allowed in every leaf marked "choices". All initially
colored points in both source envelopes and both closed annuli may take
any of the six labels or become blank. All other points keep their original
state. The annuli contain every unit neighbor of the source envelopes.
Regions can split into arbitrary measurable parts. Every inserted point
forces the erasure of a different old point by a piecewise translation.

The exact containment checks apply to parts64.json and, by a validated
padding relative to its chord mesh, to the curved Parts model as well.
"""
import argparse
import json
from fractions import Fraction as F
from itertools import product
from math import ceil, floor, lcm
from pathlib import Path
from check_exchange import inscribed
from ideal_proxy import check as check_proxy
from verify import edges, read_point

CENTERS = [(F(0), F(0)), (F('.87209'), F(0))]
HALF_SIZES = [(F('.0055'), F('.0134')), (F('.00060'), F('.0034'))]
ANNULUS = (F('.94'), F('1.06'))
SOURCES = [(x-w,x+w,y-h,y+h) for (x,y),(w,h) in zip(CENTERS,HALF_SIZES)]


def translate(b,uv):
    x,y=uv
    return b[0]+x,b[1]+x,b[2]+y,b[3]+y


def overlap(a,b):
    return a[0]<b[1] and b[0]<a[1] and a[2]<b[3] and b[2]<a[3]


def quarter(b, i):
    x,X,y,Y=b
    u,v=(x+X)/2,(y+Y)/2
    return ((x,u) if i&1==0 else (u,X))+((y,v) if i&2==0 else (v,Y))


def unit(code):
    sg,k=code
    if sg not in (1,-1) or type(k) is not int:
        raise ValueError('Invalid rational direction')
    t=F(k,10**7)
    return sg*(1-t*t)/(1+t*t),2*t/(1+t*t)


def outside(box,center,band):
    a,b,c,d=box
    x,y=center
    mn=max(0,x-b,a-x)**2+max(0,y-d,c-y)**2
    mx=max(abs(x-a),abs(x-b))**2+max(abs(y-c),abs(y-d))**2
    return mx<band[0]**2 or mn>band[1]**2


class Geometry:
    def __init__(self, spec):
        self.spec=spec
        self.sources=SOURCES
        u,v=map(read_point,spec['period'])
        assert v[0]==0 and v[1]==F(3,2) and u[1]==F(3,4)
        # Rectangular superperiod (4u-2v,4v), centered at the A hole.
        bounds=check_proxy(spec)
        assert bounds['vertices']+3*bounds['period_x']<F(1,10**11)
        self.W=min(4*u[0],8*bounds['x_lo'])
        self.H=4*v[1]
        raw=[[read_point(p) for p in s['vertices']] for s in spec['pieces']]
        self.den=lcm(*(t.denominator for q in raw for p in q for t in p))
        self.pad=ceil(self.den*F(1,10**11))
        self.segs=[edges([tuple(int(t*self.den) for t in p) for p in q]) for q in raw]
        self.colors=[s['color'] for s in spec['pieces']]
        assert set(self.colors)==set(range(1,7))
        self.lifts=[]
        for i,poly in enumerate(raw):
            xs,ys=zip(*poly)
            for m,n in product(range(-3,4),range(-5,6)):
                dx,dy=m*u[0],m*u[1]+n*v[1]
                self.lifts.append((self.colors[i],i,dx,dy,(min(xs)+dx,max(xs)+dx,min(ys)+dy,max(ys)+dy)))
        # All editable regions are strictly away from the one-unit collar.
        for (x,y),box in zip(CENTERS,SOURCES):
            assert max(abs(x)+ANNULUS[1],abs(box[0]),abs(box[1])) < self.W/2-1
            assert max(abs(y)+ANNULUS[1],abs(box[2]),abs(box[3])) < self.H/2-1
            assert max(abs(x-box[0]),abs(x-box[1]))**2 + max(abs(y-box[2]),abs(y-box[3]))**2 < (1-ANNULUS[0])**2
        # Every immediate unit witness is consequently in an editable annulus.

    def contains(self,box,color):
        a,b,c,d=box
        for col,i,dx,dy,(lx,rx,ly,ry) in self.lifts:
            if col!=color or not (lx<a<=b<rx and ly<c<=d<ry):
                continue
            x,X=floor((a-dx)*self.den),ceil((b-dx)*self.den)
            y,Y=floor((c-dy)*self.den),ceil((d-dy)*self.den)
            # All enumerated tile lifts have |m|<=3 and arbitrary vertical
            # offsets are exact. This padding certifies membership in both
            # the rational tile and its ideal counterpart via winding number.
            h=self.pad
            if inscribed(x-h,y-h,X-x+2*h,Y-y+2*h,self.segs[i]):
                return True
        return False

    def collision(self,box,previous,temporary):
        return any(overlap(box,q) for q in previous+temporary+self.sources)

    def reserve(self,box):
        # Sparse supercells compare their finite list of image boxes directly.
        pass

    def filter_numeric(self,z,labels):
        import numpy as np
        for x,y in CENTERS:
            rad=abs(z-complex(float(x),float(y)))
            labels[(rad>=float(ANNULUS[0])-.007)&(rad<=float(ANNULUS[1])+.007)]=0
        labels[(abs(z.real)>=float(self.W/2)-.01)|(abs(z.imag)>=float(self.H/2)-.01)]=0

    def frozen(self,box):
        # All second-step sites are within two units of a source. Containment
        # in the chosen fundamental block makes other blocks' edit sets disjoint.
        return (-self.W/2 <box[0]<=box[1]<self.W/2 and -self.H/2<box[2]<=box[3]<self.H/2 and
                all(not overlap(box,b) for b in SOURCES) and
                all(outside(box,c,ANNULUS) for c in CENTERS))


def check(g,data):
    images=[]
    sources=[]
    total=F(0)
    occupied=unresolved=awarded=0
    charged_area=F(0)
    unclassified_area=F(0)
    for row in data:
        s,path=row['source'],row['path']
        if s not in range(len(g.sources)) or any(k not in range(4) for k in path):
            raise ValueError('Invalid adaptive region')
        b=g.sources[s]
        for k in path:
            b=quarter(b,k)
        assert not any(overlap(b,q) for q in sources)
        sources.append(b)
        total+=(b[1]-b[0])*(b[3]-b[2])
        if 'choices' not in row:
            if 'occupied' in row:
                assert g.contains(b,row['occupied'])
                occupied+=1
            else:
                assert row.get('blank_frozen') is True
                unresolved+=1
                unclassified_area+=(b[1]-b[0])*(b[3]-b[2])
            continue
        awarded+=1
        charged_area+=(b[1]-b[0])*(b[3]-b[2])
        assert len(row['choices'])==6
        for col,(code,stops) in enumerate(row['choices'],1):
            im=translate(b,unit(code))
            assert -g.W/2 < im[0] < im[1] < g.W/2 and -g.H/2 < im[2] < im[3] < g.H/2
            assert g.contains(im,col) and not g.collision(im,images,[])
            g.reserve(im)
            images.append(im)
            other=[c for c in range(1,7) if c!=col]
            assert len(stops)==5
            for label,action in zip(other,stops):
                dest=translate(im,unit(action))
                assert g.frozen(dest) and g.contains(dest,label)
    assert total==sum((b[1]-b[0])*(b[3]-b[2]) for b in g.sources)
    return {'baselines':['rational polygon','ideal curved'],'adaptive_cells':len(sources),'charge_images':len(images),
            'frozen_witness_tests':5*len(images),'chargeable_leaves':awarded,'occupied_leaves':occupied,'other_leaves':unresolved,
            'mutable_blank_area':str(charged_area),
            'net_gain_upper_bound_if_all_envelope_blanks_editable':str(unclassified_area),
            'maximum_net_area_gain':0}


def discover(g,levels,seed=None,target=None):
    import numpy as np
    from functools import lru_cache
    from spindle_search import classifier
    classify=classifier(g.spec)
    # Floating point proposes directions only. The acceptance path uses
    # exact containment, interval exclusion and disjointness above.
    theta=np.arange(8192)*2*np.pi/8192
    dirs=np.exp(1j*theta)
    signs=np.where(dirs.real>=0,1,-1)
    pars=np.rint(10**7*dirs.imag/(1+abs(dirs.real))).astype(int)
    codes=[(int(a),int(b)) for a,b in zip(signs,pars)]
    @lru_cache(maxsize=12)
    def inventory(box,anchor):
        c=(float(box[0]+box[1])+1j*float(box[2]+box[3]))/2
        z=c+dirs
        labels,clear=classify(z)
        if anchor:
            g.filter_numeric(z,labels)
        return labels,clear
    def candidates(box,want,anchor):
        labels,clear=inventory(box,anchor)
        opts=np.flatnonzero(labels==want)
        indices=opts[np.argsort(-clear[opts])]
        # Spread probes across candidate arcs if the deepest witnesses fail.
        rank=list(range(min(16,len(indices))))+list(range(16,len(indices),max(1,len(indices)//80)))
        for j in rank:
            idx=indices[j]
            code=codes[idx]; dest=translate(box,unit(code))
            if anchor and not g.frozen(dest):
                continue
            if g.contains(dest,want):
                yield code,dest
    result=[]
    images=[]
    cache={}
    def attempt(s,path,box):
        c0=next((c for c in range(1,7) if g.contains(box,c)),None)
        if c0 is not None:
            result.append({'source':s,'path':path,'occupied':c0})
            return
        added=[]
        choices=[]
        for col in range(1,7):
            proposals=cache.get((s,col),[])[:]
            def candidates_and_cache():
                for code,stops in proposals:
                    im=translate(box,unit(code))
                    if g.contains(im,col):
                        yield code,im,stops
                for code,im in candidates(box,col,False):
                    yield code,im,None
            for code,im,stored in candidates_and_cache():
                if g.collision(im,images,added):
                    continue
                others=[c for c in range(1,7) if c!=col]
                if stored is not None:
                    dests=[translate(im,unit(k)) for k in stored]
                    if not all(g.frozen(d) and g.contains(d,c) for d,c in zip(dests,others)):
                        continue
                    steps=stored
                else:
                    available,_=inventory(im,True)
                    if not all(np.any(available==cc) for cc in others):
                        continue
                    stops=[next(candidates(im,cc,True),None) for cc in others]
                    if not all(stops):
                        continue
                    steps=[z[0] for z in stops]
                added.append(im)
                choices.append([code,steps])
                break
            else:
                break
        if len(choices)==6:
            images.extend(added)
            for im in added:
                g.reserve(im)
            for c,choice in enumerate(choices,1):
                ls=cache.setdefault((s,c),[])
                if choice not in ls:
                    ls.append(choice)
            result.append({'source':s,'path':path,'choices':choices})
        elif len(path)<levels:
            for k in range(4):
                attempt(s,path+[k],quarter(box,k))
        else:
            result.append({'source':s,'path':path,'blank_frozen':True})
    if seed is None:
        for i,b in enumerate(g.sources):
            attempt(i,[],b)
        return result

    def box_of(row):
        b=g.sources[row['source']]
        for k in row['path']:
            b=quarter(b,k)
        return b
    pending=[]
    reached=[]
    for row in seed:
        b=box_of(row)
        if 'blank_frozen' in row:
            pending.append((row,b))
            continue
        result.append(row)
        if 'choices' in row:
            reached.append(b)
            for col,choice in enumerate(row['choices'],1):
                im=translate(b,unit(choice[0]))
                g.reserve(im)
                images.append(im)
                steps=cache.setdefault((row['source'],col),[])
                if choice not in steps:
                    steps.append(choice)
    # Extend first along the frontier of already chargeable regions.
    def distance(b,c):
        return max(0,b[0]-c[1],c[0]-b[1])**2+max(0,b[2]-c[3],c[2]-b[3])**2
    def measure(b):
        return (b[1]-b[0])*(b[3]-b[2])
    pending.sort(key=lambda rb:min(distance(rb[1],c) for c in reached))
    covered=sum(measure(b) for b in reached)
    for row,b in pending:
        if target is not None and covered>target:
            result.append(row)
            continue
        start=len(result)
        attempt(row['source'],row['path'],b)
        covered+=sum(measure(box_of(leaf)) for leaf in result[start:] if 'choices' in leaf)
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--pattern',type=Path,default=Path('parts64.json'))
    p.add_argument('--certificate',type=Path,default=Path('adaptive_recolor.json'))
    p.add_argument('--search',action='store_true')
    p.add_argument('--levels',type=int,default=5)
    a=p.parse_args()
    geo=Geometry(json.loads(a.pattern.read_text()))
    data=discover(geo,a.levels) if a.search else json.loads(a.certificate.read_text())
    print(json.dumps(check(geo,data),indent=2))
    if a.search:
        a.certificate.write_text(json.dumps(data)+'\n')
