"""Exact integral Rayleigh-quotient bounds for a group-developed block."""
import numpy as np


def coefficients(labels, characters):
    """Return coset sums of autocorrelations of integral Gaussian test vectors."""
    x,y=np.indices((7,19))
    re,im,norm=[],[],[]
    for a,b in characters:
        angle=2*np.pi*(a*x/7+b*y/19)
        c=np.rint(8*np.cos(angle)).astype(np.int64)
        s=np.rint(8*np.sin(angle)).astype(np.int64)
        real=np.zeros(int(labels.max())+1,dtype=np.int64)
        imaginary=np.zeros_like(real)
        for i,j in np.ndindex(7,19):
            cr=np.roll(c,(i,j),(0,1))
            sr=np.roll(s,(i,j),(0,1))
            real[labels[i,j]]+=np.sum(c*cr+s*sr)
            imaginary[labels[i,j]]+=np.sum(c*sr-s*cr)
        re.append(real)
        im.append(imaginary)
        norm.append(np.sum(c*c+s*s))
    return np.array(re).T,np.array(im).T,np.array(norm)


def within(u, tests):
    real,imaginary,norm=tests
    cutoff=4792*norm**2
    keep=np.empty(len(u),dtype=bool)
    for i in range(0,len(u),16384):
        batch=u[i:i+16384]
        x=batch @ real
        y=batch @ imaginary
        keep[i:i+len(batch)]=np.all(x*x+y*y<=cutoff,axis=1)
    return u[keep]
