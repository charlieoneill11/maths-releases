"""Independent Arb enclosures for the twelve-mode kernel and both classical bridge slabs.

Run with python-flint and Python assertions enabled. All numerical bounds use real
ball arithmetic. The Fourier samples use the sinc integral of each cosine mode.
Besides the kernel and the two slab margins it checks, separately from
check_classical_bridge.py, the uniform explicit-formula error budget on
[35e12, 6e14] and the comparison with Carneiro--Milinovich--Soundararajan
(Theorem 5) that covers every real x >= 6e14.
"""
from flint import arb, ctx


COEFFICIENTS = (462994, 232962, 17574, -31174, 472, 7016,
                -1460, -974, 377, -20, 3, -11)


def kernel_bounds(modes):
    # A dyadic grid different from the original checker. At an endpoint of the
    # removable-pole formula the normalized sinc sum is still well defined.
    grid = 4096
    h = arb(1) / grid
    limit = 16
    pi = arb.pi()
    curvature = (2 * pi)**2 * (arb(16) / 3) * sum(abs(w) for k, w in modes)
    correction = curvature * h**2 / 8

    def transform(y):
        return sum(2 * w * ((4*y - arb(k)/2).sinc_pi() + (4*y + arb(k)/2).sinc_pi())
                   for k, w in modes)

    pole = transform(arb(0))
    left = pole
    left_primitive = arb(0)
    norm = arb(0)
    moment = arb(0)
    for index in range(1, limit*grid + 1):
        y = index*h
        right = transform(y)
        norm += h * (abs(left) + abs(right) + 2*correction)
        # The log weight has constant sign on the cell. For negative log use
        # a lower bound on |F|; for positive log use an upper bound.
        primitive = y * (y.log() - 1)
        if index <= grid:
            same_sign = (left > 0 and right > 0) or (left < 0 and right < 0)
            weight = (abs(left).min(abs(right)) - correction).max(arb(0)) if same_sign else arb(0)
        else:
            weight = abs(left).max(abs(right)) + correction
        moment += 2*weight*(primitive - left_primitive)
        left, left_primitive = right, primitive

    # The first two terms of the rational transform give an envelope
    # c2/y^2+c4/y^4 for y >= limit; integrate the tails over both signs.
    c2 = abs(sum((-1)**j*k*w for j, (k, w) in enumerate(modes))) / (8*pi)
    c4 = sum(k**3*abs(w) for k, w in modes) / (512*pi*(1-(arb(23)/(8*limit))**2))
    for exponent, coefficient in ((1, c2), (3, c4)):
        mass = 2*coefficient / (exponent * limit**exponent)
        norm += mass
        moment += mass * (arb(limit).log() + arb(1)/exponent)
    assert pole > arb('1.00000063')
    assert norm < arb('.765870')
    assert moment + arb('2e-6') < arb('-1.37957')
    print('F(0), norm upper bound, log moment upper bound:',
          pole.str(18), norm.upper().str(18), moment.upper().str(18))
    return pole


def shoulder_layers(modes):
    grid = 4000
    h = arb(1)/grid
    pi = arb.pi()
    assert sum(abs(w)*(pi*k/4)**2 for k, w in modes) < 16
    # Use the same fixed 2 h² interpolation allowance as the primary checker.
    allowance = 2*h**2
    last_height = arb(0)
    last_value = arb(0)  # G(2) = 0
    layers = []
    for j in range(grid, 0, -1):
        v = j*h
        t = 1 + (j-1)*h
        value = sum(w*(k*t/4).cos_pi() for k, w in modes).max(arb(0))
        # Choose an exact dyadic upper endpoint for each step height, so layer
        # differences are nonnegative even on constant portions of the envelope.
        height = (value.max(last_value) + allowance).upper()
        if height > last_height:
            layers.append((v, height - last_height))
            last_height = height
        last_value = value
    assert last_height < arb('.76')
    return layers


def check_slab(left, right, upper_log, p0, k, max_charge, min_margin, min_derivative, layers, pole):
    s = arb(11)/10
    n = arb(left)
    lower_log, upper_log = arb('34.2'), arb(upper_log)
    u = 1 + arb('1e-10')
    p0, k = arb(p0), arb(k)
    scale = s*n.root(10)*n/(n+1)
    assert p0 < scale
    assert lower_log < s*n.log() and s*arb(right+1).log() < upper_log
    assert p0 * n*n.root(10) / (4000*u) > 10**12
    charge = arb(0)
    for v, drop in layers:
        offset = (p0*v/u).log()
        assert lower_log + offset > 0
        # Extremize over both endpoints without any sign decision for the offset.
        ratio = (lower_log/(lower_log+offset)).max(upper_log/(upper_log+offset))
        charge += 8*u**2 * drop*v*ratio
    margin = k*scale - arb('.765870')*((n+1)/s).log() + arb('1.37957')
    derivative = k*(s-1)*scale - arb('.765870')
    assert charge < arb(max_charge) and pole-charge > k
    assert margin > arb(min_margin) and derivative > arb(min_derivative)
    print(f'{left}..{right} charge upper, margin lower, derivative lower:',
          charge.upper().str(18), margin.lower().str(18), derivative.lower().str(18))


def error_budget(modes):
    """The error terms of the gap inequality, uniformly on [35e12, 6e14].

    Follows the proof of the twelve-mode proposition: K = 2, U = 1 + 1e-12,
    D <= 1.1/l, log(2 pi/D) <= log(7 (r+1)/1.1), log a + K D < 2*37.5 + 1,
    sqrt(a) >= l^(11/10), P < 34, and the bounds V_0 < 625, V_1 < 2000.
    """
    pi = arb.pi()
    left, right = arb(35*10**12), arb(600*10**12)
    big_k = 2
    u = 1 + arb('1e-12')
    weight = sum(abs(w) for k, w in modes)
    assert weight < 1 and 2*big_k*weight < 4                 # sum|w| < 1, ||G||_1 < 4
    # Hypothesis (H) on the whole range: log a >= 60, K D <= (U-1)/U, K P < 100.
    d_max = arb('1.1')/left
    root_min = left*left.root(10)                            # sqrt(a) >= x^(11/10)
    p_max = arb('1.1')*(right + 1)*(right + 1).root(10)/right   # (x+1)^(11/10)/x increases
    assert arb('2.2')*left.log() > 68
    assert big_k*d_max < (u - 1)/u                          # gives e^{KD} < U
    assert p_max < 34 and big_k*p_max < 100
    # V_0 and V_1 from |F'| <= 2 pi K^2 sum|w| and the rational tail beyond 16.
    derivative = 2*pi*big_k**2*weight
    assert derivative < 39
    lam0 = 1 - (arb(23)/128)**2
    kappa1 = sum(k*abs(w) for k, w in modes)
    tail = 8/pi*kappa1/64*(4*pi/lam0 + arb(2)/(16*lam0**2))
    assert tail < 2                                          # |F'(y)| < 2/y^2 for y >= 16
    log16 = arb(16).log()
    v0 = 16*39 + arb(2)/16
    v1 = 39*(16*log16 - 15) + (log16 + 1)/8
    assert v0 < 625 and v1 < 2000
    # Prime powers and endpoints: E_pow with ell < 76.
    ell = arb(76)
    assert arb('2.2')*(right + 1).log() + big_k*d_max < ell
    e_pow = (2 + ell/arb(2).log()*(1 + big_k*p_max*u))*ell*u/root_min
    # Zeros: 2D[(3 + 0.15 log(2 pi/D)) V_0 + 0.15 V_1 + 4], with 2 pi < 7.
    assert 2*pi < 7
    zeros = 2*d_max*((3 + arb('0.15')*(7*(right + 1)/arb('1.1')).log())*625
                     + arb('0.15')*2000 + 4)
    # The +1 in each Brun--Titchmarsh count: 4 U^2 e_1 lambda_+ e^{-L}.
    endpoints = 4*u**2*arb('0.76')*arb('37.5')/root_min
    # The two tiny terms absorbed by 1e-12: the pole and the trivial zeros.
    norm_g = 2*big_k*weight
    pole = p_max*norm_g*(big_k*d_max)**2/4
    support_min = root_min**2/u                              # a e^{-KD} > a/U
    trivial = d_max*norm_g*2*support_min**arb('-2.5')        # geometric series, ratio < 1/2
    assert pole < arb('1e-22') and trivial < arb('1e-20')
    total = e_pow + zeros + endpoints + arb('1e-12')
    assert e_pow < arb('7.3e-10') and zeros < arb('3.6e-10') and endpoints < arb('1.5e-13')
    assert total < arb('1.1e-9') and arb('1.1e-9') < arb('2e-6')
    print('error budget on [35e12, 6e14]: E_pow, zeros, endpoints, total upper bounds:',
          e_pow.upper().str(6), zeros.upper().str(6), endpoints.upper().str(6),
          total.upper().str(6))


def cms_tail():
    """Corollary: every real x >= 6e14, via Carneiro--Milinovich--Soundararajan."""
    x = arb(600*10**12)
    eps = arb('2e-15')
    assert arb('1.1')/x < arb('1.9e-15')
    assert (arb('1.1')/x).exp() < 1 + eps                   # (1+1/x)^(11/10) <= e^{1.1/x}
    assert (1 + 1/x).log() < eps
    assert arb(1)/2 < arb('2e-17')*arb(11)/5*x**(arb(11)/10)
    root = x.root(10)
    assert root > arb('8.8')*(1 + eps)                       # left side increases beyond x
    margin = root - arb(22)/25*(1 + eps)*(x.log() + eps) - arb('2e-17')
    assert margin > arb('0.1')
    print('x >= 6e14: CMS comparison margin lower bound', margin.lower().str(12))


def main():
    if not __debug__:
        raise SystemExit('Run with Python assertions enabled.')
    ctx.prec = 112
    modes = [(2*j+1, arb(v)/10**6) for j, v in enumerate(COEFFICIENTS)]
    pole = kernel_bounds(modes)
    layers = shoulder_layers(modes)
    error_budget(modes)
    trillion = 10**12
    check_slab(35*trillion, 37*trillion, '34.4', '24.877', '.90184',
               '.098159', '.0030', '1.4776', layers, pole)
    check_slab(37*trillion, 600*trillion, '37.5', '25.015', '.90150',
               '.098420', '.0769', '1.4892', layers, pole)
    cms_tail()


if __name__ == '__main__':
    main()
