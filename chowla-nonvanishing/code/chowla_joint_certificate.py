"""Exact rational certificate for a mixed-statistic nonvanishing bound.

The Fourier tests have the shape sum c_j P_{2j}(x/sigma) on [-sigma,sigma].
The twenty rows give the random part. The final row is the deterministic
projection, subtracted from the random part. All spline operations and bounds
are rational. No external packages are required.
"""
from fractions import Fraction as Q
from math import comb, factorial
from functools import cache

rows = [
    [-36,-54,-66,-67,-57,-41,-16], [-38,-55,-65,-65,-51,-32,-4],
    [-39,-54,-62,-60,-42,-23,4], [-40,-54,-60,-55,-35,-14,10],
    [-41,-54,-58,-51,-28,-7,14], [-42,-53,-56,-47,-22,1,17],
    [-42,-51,-53,-42,-17,7,20], [-41,-50,-50,-37,-12,12,21],
    [-41,-48,-48,-32,-7,17,23], [-41,-46,-46,-27,-3,21,23],
    [-40,-44,-44,-23,1,24,23], [-39,-42,-41,-19,5,27,22],
    [-38,-39,-39,-16,8,30,20], [-37,-36,-36,-14,10,31,19],
    [-37,-34,-33,-11,12,31,20], [-36,-31,-30,-8,13,30,19],
    [-35,-30,-27,-6,16,29,17], [-34,-27,-24,-4,18,28,12],
    [-31,-23,-20,-3,17,26,11], [-100,25,21,17,16,5,-11],
]
projection = [-67,-8,37,-8,20,-2,10]


def jumps(polynomial, endpoint):
    """Return all derivatives of an ascending-coefficient polynomial."""
    return tuple(sum(p*Q(factorial(k),factorial(k-j))*endpoint**(k-j)
                     for k,p in enumerate(polynomial) if k>=j)
                 for j in range(len(polynomial)))


def segment(polynomial, left, right):
    """Encode the restriction using truncated powers (x-a)_+^j / j!."""
    return [(left, jumps(polynomial,left)),
            (right, tuple(-p for p in jumps(polynomial,right)))]


def legendre_test(row, sigma):
    p = [Q(0)]*(2*len(row)+1)
    for j,c in enumerate(row,1):
        n = 2*j
        for k in range(j+1):
            degree = n-2*k
            p[degree] += Q(c*(-1)**k*comb(n,k)*comb(2*n-2*k,n),
                           2**n*sigma**degree)
    return segment(p,-sigma,sigma)


def approximate_H():
    # H = A cos(u/2) + (1/4-A) sin(u/2), u=|x|, A=(1+cot(1/4))/8.
    # Alternating partial sums of sine and cosine certify A to < 5e-15.
    z = Q(1,4)
    cos6 = sum((-1)**k*z**(2*k)/factorial(2*k) for k in range(7))
    sin6 = sum((-1)**k*z**(2*k+1)/factorial(2*k+1) for k in range(7))
    cos7 = cos6-z**14/factorial(14)
    sin7 = sin6-z**15/factorial(15)
    A = Q(61453967058074,10**14)
    lo, hi = (1+cos7/sin6)/8, (1+cos6/sin7)/8
    assert max(abs(A-lo),abs(A-hi)) < Q(5,10**15)
    # The Taylor remainders at |x|/2 <= 1/2, plus twice the coefficient
    # error, bound the uniform error of the two polynomial pieces.
    err = (Q(1,2)**14/factorial(14) + Q(1,2)**13/factorial(13)
           + Q(1,10**14))
    assert err < Q(1,10**12)
    p = tuple((A if k%2==0 else z-A)*(-1)**(k//2) / (2**k*factorial(k))
              for k in range(13))
    return segment(tuple(c*(-1)**k for k,c in enumerate(p)),-1,0)+segment(p,0,1)


def convolution(left, right):
    out = {}
    for x,px in left:
        for y,py in right:
            a = x+y
            poly = out.setdefault(a,[Q(0)]*(len(px)+len(py)))
            for j,c in enumerate(px):
                for k,d in enumerate(py):
                    poly[j+k+1] += c*d
    def antiderivative(n,t):
        # n-fold primitive, with zero constants to the left of the support.
        value = Q(0)
        for a,poly in out.items():
            if t>a:
                b = t-a
                h = Q(0)
                for k in range(len(poly)-1,-1,-1):
                    h = h*b + poly[k]/factorial(k+n)
                value += h*b**n
        return value
    return cache(antiderivative)


def integrate(f,l,r,power=0,origin=0,shift=0,sign=1):
    """Integrate (v-origin)^power f(shift+sign*v) by parts."""
    if r<=l:
        return Q(0)
    def end(x):
        return sum((-1)**j*(x-origin)**(power-j)*Q(factorial(power),factorial(power-j))
                   *f(j+1,shift+sign*x)*sign**(j+1) for j in range(power+1))
    return end(r)-end(l)


def covariance(f,t):
    # Covariance of S_h and S_Tt, f is the Fourier transform of h.
    return (4*integrate(f,0,t,1)
            -2*integrate(f,1-t,1,1,1-t)+2*integrate(f,1,1+t,1,1+t))


def mean(f):
    return f(0,0)-integrate(f,0,1)


def pair(f,a,b):
    m = min(a,b)
    pieces = [(Q(0),1,m),(a-m,2,-Q(1,2)),(a,2,Q(1,2)),
              (b-m,2,-Q(1,2)),(b,2,Q(1,2)),
              (a+b-2*m,2,Q(1,4)),(a+b,2,-Q(1,4))]
    k = sum(c*(integrate(f,l,a+b,p,l,1,-1)-integrate(f,l,a+b,p,l,1,1))
            for l,p,c in pieces)
    return 2*m*m*mean(f)+8*k


def main():
    ts = [Q(i+1,40) for i in range(len(rows))]
    rs = [legendre_test(row,1-t) for row,t in zip(rows,ts)]
    g = legendre_test(projection,Q(1))
    H = approximate_H()
    C = sum(covariance(convolution(H,r),t) for r,t in zip(rs,ts))
    error = Q(1,10**12)*sum(8*t*t*(1-t)*sum(map(abs,row)) for t,row in zip(ts,rows))
    M = sum((1 if i==j else 2)*pair(convolution(r,s),a,b)
            for i,(r,a) in enumerate(zip(rs,ts)) for j,(s,b) in enumerate(zip(rs[:i+1],ts[:i+1])))
    cross = sum(covariance(convolution(g,r),t) for r,t in zip(rs,ts))
    norm = mean(convolution(g,g))
    D = M-2*cross+norm
    assert C>error and D>0
    gain = (C-error)**2/(2*D)
    assert C-error > Q(3915746,10**6) and D < Q(37364531,10**4)
    assert gain > Q(20518,10**7)
    print('C >',float(C-error),'D =',float(D),'gain >',float(gain))
    print('Exact rational comparisons certify a gain above 0.0020518.')


if __name__=='__main__':
    main()
