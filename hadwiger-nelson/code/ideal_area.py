"""Enclose the ideal Parts area at a fixed n near its stationary value.

Interval operations use integers on a uniform grid with outward rounding.
The endpoint signs and intermediate value theorem prove existence of m for
which the inner rectangles and the outer-pair constraints close. This
checks the ideal area formula, not simplicity or separation of the tiles.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import isqrt

D = 10**65


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    @staticmethod
    def num(value):
        if isinstance(value, Interval):
            return value
        q = Fraction(value)*D
        return Interval(q.numerator//q.denominator, -(-q.numerator//q.denominator))

    def __add__(self, other):
        other = self.num(other)
        return Interval(self.lo+other.lo, self.hi+other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-self.num(other))

    def __rsub__(self, other):
        return self.num(other) + (-self)

    def __mul__(self, other):
        other = self.num(other)
        p = [i*j for i in (self.lo,self.hi) for j in (other.lo,other.hi)]
        return Interval(min(p)//D, -(-max(p)//D))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.num(other)
        if other.lo * other.hi <= 0:
            raise ZeroDivisionError
        return self * Interval(D**2//other.hi, -(-D**2//other.lo))

    def __rtruediv__(self, other):
        return self.num(other) / self

    def sqrt(self):
        return Interval(isqrt(self.lo*D), 1+isqrt(self.hi*D))


def arcsin(x):
    # Positive Taylor terms with recurrence t[k+1]/t[k] <= x^2.
    assert 0 <= x.lo <= x.hi < D
    term = result = x
    for k in range(15):
        term = term*x*x*(2*k+1)**2/((2*k+2)*(2*k+3))
        result += term
    tail = term*x*x/(1-x*x)
    return result + Interval(0,tail.hi)


def compute(n,m):
    y = Interval.num('0.5')
    l = m+n
    uy = (3*y/2+l)/2
    ux = (1-uy*uy).sqrt()
    leg = lambda h: (1-h*h).sqrt()
    p = (leg(y/2-l)-leg(y/2+n-m))/2
    q = p+(m-n)*uy/ux
    x = ux-(p+q)/2
    d = (leg(y-2*n)-leg(y))/2
    r = q+d
    z = (x-leg(y)-q-2*d)/(1-4*n/y)
    s = d-4*n*z/y
    t = 4*n*z/y-p
    residual = (x+z-t)*(x+z-t)+(y/2-l)*(y/2-l)-1
    area = l*p+n*r+m*q-n*p+n*(s+t)
    for side in (p,d):
        h = (n*n+side*side).sqrt()
        area -= arcsin(h)-h*leg(h)
    return residual,area/(x*y)


def report():
    n = Interval.num('0.0033448254428846693594959344084790204661219925262831')
    low = Interval.num('0.00999872202647143777010571984520501496174154458')
    high = low + Interval.num('0.00000000000000000000000000000000000000000000001')
    s0,s1 = compute(n,low)[0],compute(n,high)[0]
    assert s0.hi < 0 < s1.lo or s1.hi < 0 < s0.lo
    bound = compute(n,Interval(low.lo, high.hi))[1]
    # Present decimal endpoints exactly (all interval values are on a fixed grid).
    for name,value in [('epsilon',bound),('rho',1/bound)]:
        digits = 40
        k = D//(10**digits)
        dec = lambda i: str(i//10**digits)+'.'+str(i%10**digits).zfill(digits)
        print(name, '[',dec(value.lo//k),',',dec(-(-value.hi//k)),']')


if __name__ == '__main__':
    report()
