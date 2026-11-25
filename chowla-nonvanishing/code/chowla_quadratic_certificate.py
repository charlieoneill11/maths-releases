"""Exact fourth- and fifth-moment improvement using ERR's restricted cumulants.

Requires chowla_joint_certificate.py in the same directory and Python 3.
Functions prefixed by f below are Fourier splines represented by their
primitives to the left of the support, as in the companion certificate.
"""
from collections import Counter
from fractions import Fraction as Q
from math import comb, factorial
import chowla_joint_certificate as j

# Ordered by 1 <= i <= k <= 5, a=i/20, b=k/20.
# Coefficients of P2,P4,...,P10 of u/(1-a-b).
quadratic_rows = [
    [7,24,50,55,36], [17,52,100,85,14], [23,54,88,53,-28],
    [28,49,61,15,-41], [74,5,15,-43,4], [11,29,46,30,-19],
    [31,59,74,33,-71], [31,48,43,13,-74], [82,5,-4,-48,10],
    [18,28,25,15,-50], [35,42,14,25,-89], [69,10,-11,-50,22],
    [20,17,-15,2,-22], [34,1,-13,-32,27], [-24,29,-21,16,-4],
]

# Fourier coefficients for deterministic and linear parts.
joint_projection = [-7383, -544, 3924, -1058, 2349, -310, 1151]
joint_linear_rows = [
    [-4095, -6055, -7451, -7635, -6446, -4624, -1830],
    [-5353, -5870, -7289, -7010, -4876, -3883, -265],
    [-4295, -5916, -6947, -6687, -4592, -2510, 553],
    [-5426, -5680, -6399, -5872, -3060, -1912, 1241],
    [-4386, -5653, -6318, -5658, -2976, -747, 1706],
    [-5281, -5509, -5672, -4806, -1845, -128, 1869],
    [-4405, -5320, -5672, -4600, -1747, 674, 2281],
    [-4986, -5225, -5091, -3751, -1092, 1251, 2328],
    [-4403, -5000, -5132, -3521, -739, 1815, 2529],
    [-4760, -4838, -4746, -2452, -599, 2214, 2582],
    [-4310, -4581, -4671, -2529, 131, 2658, 2457],
    [-4229, -4321, -4440, -2111, 501, 2974, 2311],
    [-4136, -4035, -4189, -1753, 806, 3219, 2171],
    [-4039, -3739, -3906, -1443, 1032, 3354, 2085],
    [-3955, -3467, -3603, -1158, 1209, 3354, 2104],
    [-3885, -3240, -3296, -876, 1416, 3236, 2082],
    [-3802, -3038, -2991, -615, 1705, 3111, 1810],
    [-3629, -2767, -2637, -438, 1929, 3022, 1335],
    [-3338, -2375, -2170, -360, 1827, 2760, 1192],
    [-10571, 2532, 2287, 1781, 1735, 586, -1200],
]

# Ordered by 1 <= i <= k <= 5, a=i/20, b=k/20.
# Coefficients of P2,P4,...,P10 of u/(1-a-b).
joint_quadratic_rows = [
    [1099, 3234, 6416, 6862, 4052],
    [2401, 6609, 12164, 10393, 810],
    [2987, 6675, 10389, 6465, -4027],
    [3634, 6155, 7290, 1877, -5249],
    [9532, 702, 1935, -5827, 656],
    [1523, 3515, 5419, 3647, -2663],
    [3890, 7087, 8222, 4047, -8939],
    [3974, 5836, 4753, 1493, -8636],
    [9820, 507, -2, -6270, 1342],
    [2115, 3237, 2608, 1652, -5806],
    [4140, 5009, 1368, 2426, -9952],
    [8077, 843, -957, -6125, 2564],
    [2286, 2047, -1658, 17, -2367],
    [4278, -114, -1375, -3728, 2963],
    [-2227, 3144, -2679, 1841, -440],
]


def odd_primitive(f,n,x):
    """n-fold lower primitive of sign(u)*f(u), with f even."""
    if x<0:
        return -f(n,x)
    return f(n,x)-2*sum(x**k*f(n-k,0)/factorial(k) for k in range(n))


def cumulant(f,widths):
    """Restricted joint cumulant with m>=2 rectangle Fourier tests.

    The remaining test has the even Fourier transform f(0,u).
    """
    shifts = {Q(0):1}
    for width in widths:
        next_shifts = Counter()
        for s,c in shifts.items():
            next_shifts[s] += 2*c
            next_shifts[s-width] -= c
            next_shifts[s+width] -= c
        shifts = next_shifts
    n = len(widths)+1
    return Q((-2)**n,2)*sum(c*odd_primitive(f,n,1+s) for s,c in shifts.items())


def cov_rect(a,b):
    return 2*min(a,b)**2


def mixed_cross(f,t,a,b):
    return (cumulant(f,[t,a,b])+cov_rect(t,b)*j.covariance(f,a)
            +cov_rect(t,a)*j.covariance(f,b))


def quadratic_cross(f,a,b,c,d):
    return (cumulant(f,[a,b,c,d])
            +cov_rect(b,d)*cumulant(f,[a,c])+cov_rect(b,c)*cumulant(f,[a,d])
            +cov_rect(a,d)*cumulant(f,[b,c])+cov_rect(a,c)*cumulant(f,[b,d])
            +(cov_rect(a,c)*cov_rect(b,d)+cov_rect(a,d)*cov_rect(b,c))*j.mean(f))


def evaluate(projection,linear_rows,quadratic_rows,eta):
    H = j.approximate_H()
    g = j.legendre_test(projection,Q(1))
    ts = [Q(k+1,40) for k in range(len(linear_rows))]
    rs = [j.legendre_test(row,1-t) for row,t in zip(linear_rows,ts)]
    pairs = [(Q(i,20),Q(k,20)) for i in range(1,6) for k in range(i,6)]
    ps = [j.legendre_test(row,1-a-b) for row,(a,b) in zip(quadratic_rows,pairs)]

    # Calibrate signed-tail normalization against the independent sine-kernel
    # trace in the companion certificate, including unequal rectangle widths.
    for i,k in ((0,0),(0,19),(4,13),(19,19)):
        a,b = ts[i],ts[k]
        f = j.convolution(rs[i],rs[k])
        assert cumulant(f,[a,b]) == j.pair(f,a,b)-cov_rect(a,b)*j.mean(f)

    # A second normalization check integrates identical rectangles directly.
    # Choosing k negative coordinates, translating their box by k*a and
    # applying bounded-simplex inclusion-exclusion gives the binomial 2n.
    a = Q(17,50)
    def rectangle_primitive(n,x):
        return (max(Q(0),x+a)**n-max(Q(0),x-a)**n)/factorial(n)
    for n in (4,5):
        tail = sum((-1)**k*comb(2*n,k)*max(Q(0),(n-k)*a-1)**n
                   for k in range(n+1))/factorial(n)
        assert cumulant(rectangle_primitive,[a]*(n-1)) == -Q((-2)**n,2)*tail

    C1 = sum(j.covariance(j.convolution(H,r),t) for r,t in zip(rs,ts))
    M1 = sum((1 if i==k else 2)*j.pair(j.convolution(r,s),a,b)
             for i,(r,a) in enumerate(zip(rs,ts)) for k,(s,b) in enumerate(zip(rs[:i+1],ts[:i+1])))
    M1 += j.mean(j.convolution(g,g))-2*sum(j.covariance(j.convolution(g,r),t) for r,t in zip(rs,ts))
    C2 = sum(cumulant(j.convolution(H,p),[a,b]) for p,(a,b) in zip(ps,pairs))
    L12 = sum(mixed_cross(j.convolution(p,r),t,a,b) for p,(a,b) in zip(ps,pairs)
              for r,t in zip(rs,ts))
    L12 -= sum(cumulant(j.convolution(p,g),[a,b]) for p,(a,b) in zip(ps,pairs))
    M2 = sum((1 if i==k else 2)*quadratic_cross(j.convolution(p,q),a,b,c,d)
             for i,(p,(a,b)) in enumerate(zip(ps,pairs))
             for k,(q,(c,d)) in enumerate(zip(ps[:i+1],pairs[:i+1])))

    # C2 is a signed fourfold box sum (both signs for each of 3 Fourier
    # variables). Bounding the ERR integral by the product L1 norms gives
    # 4 * (2a)*(2b)* ||(H-P)*R||_1.  ||H-P||_1 <= 2e-12.
    err1 = Q(1,10**12)*sum(8*t*t*(1-t)*sum(map(abs,row)) for row,t in zip(linear_rows,ts))
    err2 = Q(1,10**12)*sum(64*a*b*(1-a-b)*sum(map(abs,row)) for row,(a,b) in zip(quadratic_rows,pairs))
    C_lower = C1 + eta*C2 - err1 - eta*err2
    D = M1 + 2*eta*L12 + eta**2*M2
    assert C_lower > 0 and D > 0
    gain = C_lower**2/(2*D)
    print('C2 =',float(C2),'L12 =',float(L12),'M2 =',float(M2))
    print('Lower bound on C =',float(C_lower),'D =',float(D))
    return C_lower,D,gain


if __name__=='__main__':
    _,_,first_gain = evaluate(j.projection,j.rows,quadratic_rows,Q(24,25))
    assert first_gain > Q(20878,10**7)
    joint_C,joint_D,joint_gain = evaluate(joint_projection,joint_linear_rows,joint_quadratic_rows,Q(1))
    assert joint_C > Q(41851245,100000) and 0 < joint_D < Q(4185150945,100)
    assert joint_gain > Q(209254,10**8)
    print('Exact arithmetic certifies an additive nonvanishing gain above 0.00209254.')
