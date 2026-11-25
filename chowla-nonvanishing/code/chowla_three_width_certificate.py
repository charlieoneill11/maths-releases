"""Exact verification of the three-width correction to the mixed-width witness.

For each triple the widths are the displayed integers divided by 160.
The two entries multiply the Fourier profiles P2 and P4 respectively,
with a common coefficient denominator of 10**9.
"""
from fractions import Fraction

import chowla_mixed_width_certificate as mixed


PROFILES = {
    (8, 12, 24): (-121717517, 491610893),
    (8, 16, 80): (-14064566, -132741707),
    (8, 24, 64): (-26652553, 174310795),
    (8, 28, 48): (-66504478, 127384262),
    (8, 48, 64): (38776636, -2023335),
    (12, 24, 48): (82266724, 130618646),
    (12, 28, 60): (185849866, 11551660),
    (12, 32, 40): (-116997456, 284382384),
    (12, 36, 84): (-3460378, 2595712),
    (12, 40, 64): (70680011, 47058362),
    (12, 52, 72): (19681327, -1896137),
    (16, 24, 72): (-33517020, -53977051),
    (16, 32, 56): (-15400926, 156214903),
    (16, 32, 80): (20845072, -13504451),
    (16, 44, 64): (28046350, 21683205),
    (20, 20, 60): (12736579, 66406823),
    (20, 36, 52): (93880390, -6395813),
    (20, 36, 68): (-11293709, -1725090),
    (24, 24, 64): (-5068851, -6379821),
    (24, 32, 72): (-43669224, 115682),
    (24, 40, 56): (-5891849, -3126459),
    (24, 48, 64): (6578063, 2318498),
    (32, 32, 64): (29119324, -19344054),
    (32, 40, 48): (27089147, -1290595),
    (32, 40, 64): (-18632458, 2244473),
    (32, 48, 64): (-2867142, 907756),
}
CERTIFIED_PROPORTION = Fraction("0.9453419890")


def certify():
    weight = Fraction(1, 10**9)
    profiles = [(dims, coefficients, weight) for dims, coefficients
                in (*mixed.PROFILES.items(), *PROFILES.items())]
    return mixed.octic.certify(profiles)


if __name__ == "__main__":
    bound = certify()
    assert bound > CERTIFIED_PROPORTION
    print(f"Verified lower limiting nonvanishing proportion above {float(CERTIFIED_PROPORTION):.10f}.")
