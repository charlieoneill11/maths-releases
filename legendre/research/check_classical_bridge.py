"""Check the twelve-mode RH comparison from 35 trillion using classical Brun–Titchmarsh."""

from fractions import Fraction as Q
from math import ceil

from check_bounded_factors import highlog, lowlog
from check_cutoffs import log_bounds, tenth_root
from check_three_mode import PI_HI, PI_LO, check_pi
from check_twelve_modes import M, upper_shoulder, verify


S = Q(11, 10)
GRID = 4000
U = Q("1.0000000001")
NORM = Q(".765870")
LOG_SAVING = Q("1.37957")
MIN_LOG = Q("34.2")
TRILLION = 10**12


def shoulder_layers():
    """Majorize G_+(1+u) by nested prefixes of the 4,000-cell grid."""
    layers = []
    right = upper_shoulder(Q(2))
    height = Q(0)
    for j in range(GRID, 0, -1):
        left = upper_shoulder(1 + Q(j - 1, GRID))
        # Linear interpolation with |G''| < 16 costs at most 2 / GRID².
        new_height = max(height, max(left, right) + Q(2, GRID**2))
        if new_height > height:
            layers.append((Q(j, GRID), new_height - height))
        height = new_height
        right = left
    assert height < Q(".76")
    return layers


def check_errors():
    """Uniform absolute errors in the explicit formula on both slabs."""
    left, right = 35 * TRILLION, 600 * TRILLION
    max_log = Q("37.5")
    min_root = left * tenth_root(left)[0]  # lower bound for sqrt(a)
    max_d = S / left
    min_d = S / (right + 1)
    # (x+1)^(11/10)/x increases for x > 10.
    max_p = S * (right + 1) * tenth_root(right + 1)[1] / right
    assert max_p < 34 and 2 * max_d < (U - 1) / U

    # Each exponent has at most 1 + 2 sqrt(a) sinh(D) integer roots.
    exponents = (2 * max_log + 1) / lowlog(2)
    roots = 1 + 2 * max_p * U
    prime_powers = (exponents * roots + 2) * (2 * max_log + 1) * U / min_root
    # The +1 in each closed-interval prime count, integrated over both shoulders.
    endpoints = 2 * Q(".76") * 2 * max_log * U / min_root

    # Bound |F'| by Fourier differentiation below 16 and the rational transform above.
    weight = sum(abs(w) for _, w in M)
    weighted_modes = sum(k * abs(w) for k, w in M)
    denominator = 1 - Q(23, 8 * 16)**2
    assert 4 * PI_HI * 4 * weight < 39
    assert 8 * weighted_modes / (64 * PI_LO) * (
        4 * PI_HI / denominator + Q(2, 16) / denominator**2
    ) < 2
    assert 16 * 39 + Q(2, 16) < 625
    log16 = highlog(16)
    assert 39 * (16 * log16 - 15) + 2 * (log16 + 1) / 16 < 2000
    # CMS zero-count discrepancy. The extension to 0 costs <= 2D ||F||_infty.
    zeros = 2 * max_d * ((3 + Q(".15") * highlog(7 / min_d)) * 625 + 300) + 8 * max_d

    # cosh(D)-1 <= D²; the support lies above a/U in physical coordinates.
    pole = max_p * 4 * max_d**2
    support_min = min_root**2 / U
    trivial_zeros = 4 * max_d / (support_min**2 - 1)
    total = prime_powers + endpoints + zeros + pole + trivial_zeros
    assert prime_powers < Q("7.3e-10") and zeros < Q("3.6e-10")
    assert endpoints < Q("1.5e-13") and total < Q("1.1e-9") < Q("2e-6")
    print(f"Explicit-formula errors < 1.1e-9 (computed upper bound about {float(total):.10g})")


def check_slab(left, right, max_log, min_p, k, max_charge, min_margin, min_derivative, layers):
    min_scale = S * tenth_root(left)[0] * left / (left + 1)
    min_root = left * tenth_root(left)[0]
    assert MIN_LOG < S * lowlog(left) and S * highlog(right + 1) < max_log
    assert min_p < min_scale and min_p * min_root / (GRID * U) > 10**12

    units = 10**20
    charge_units = 0
    for v, drop in layers:
        # A prefix has physical length at least P sqrt(a) v / U. Use 2t/log(t)+1.
        offset = lowlog(min_p * v) - highlog(U)
        log_endpoint = max_log if offset >= 0 else MIN_LOG
        assert MIN_LOG + offset > 0
        price = 8 * U**2 * drop * v * log_endpoint / (log_endpoint + offset)
        charge_units += ceil(units * price)
    charge = Q(charge_units, units)
    assert charge < max_charge and Q("1.00000063") - charge > k

    # Use Taylor-enclosed logs for the final signs, independently of the charge routine.
    margin = k * min_scale - NORM * log_bounds((left + 1) / S)[1] + LOG_SAVING
    derivative = k * (S - 1) * min_scale - NORM
    assert margin > min_margin > 0 and derivative > min_derivative > 0
    print(f"[{left}, {right}]  k = {float(k):.5f}, charge < {float(max_charge):.6f}, "
          f"g(left) > {float(min_margin):.4f}, dg/dlog(x) > {float(min_derivative):.4f}")
    print(f"  Computed bounds (approx.) {float(charge):.12f}, "
          f"{float(margin):.12f}, {float(derivative):.12f}")


def main():
    if not __debug__:
        raise SystemExit("Run with Python assertions enabled.")
    check_pi()
    verify()  # Archived Fourier norm, pole, log moment and interpolation checks.
    check_errors()
    layers = shoulder_layers()
    check_slab(35 * TRILLION, 37 * TRILLION, Q("34.4"), Q("24.877"), Q(".90184"),
               Q(".098159"), Q(".0030"), Q("1.4776"), layers)
    check_slab(37 * TRILLION, 600 * TRILLION, Q("37.5"), Q("25.015"), Q(".90150"),
               Q(".098420"), Q(".0769"), Q("1.4892"), layers)
    # CMS Theorem 5 covers the subsequent tail since x^(1/10)/log(x) increases.
    end = 600 * TRILLION
    log_lo, log_hi = log_bounds(end)
    assert log_lo > 10 and tenth_root(end)[0] > Q(22, 25) * log_hi
    # The paper's form (corollary of CMS Theorem 5): for x >= end,
    # x^(1/10) - (22/25)(1+2e-15)(log x + 2e-15) - 2e-17 > 0, increasing once
    # x^(1/10) > 8.8 (1+2e-15).
    eps = Q(2, 10**15)
    root = tenth_root(end)[0]
    tail_margin = root - Q(22, 25) * (1 + eps) * (log_hi + eps) - Q(2, 10**17)
    assert root > Q(88, 10) * (1 + eps) and tail_margin > Q(1, 10)
    print(f"x >= {end}: CMS comparison margin > 0.1 (about {float(tail_margin):.6f})")


if __name__ == "__main__":
    main()
