"""Recompute Gram entries of stages 3, 7 and 8 by a second method.

The certificates evaluate the Gram entries of stage 3 by enumerating
labelled partitions (chowla_cubic_single_certificate.inner_product) and those
of stages 4-8 by the contraction formula over cross-matchings
(chowla_one_exception_certificate.inner).  This program recomputes

  * every Gram entry of stage 3 by the contraction formula;
  * every Gram entry among the rows (R8)-(R9), and between those rows and
    the rows (R6)-(R7), by labelled cumulant partitions; and
  * 3,000 distinct entries between the rows (R8)-(R9) and the rows of F_4,
    chosen by a seeded pseudorandom generator, by labelled cumulant partitions;

and asserts exact agreement.  Both methods share the routine for the
individual marked cumulants.  Run beside the other certificate files.
"""
import random
import sys

import chowla_three_width_certificate as three
import chowla_octic_crosscheck as partitions

mixed = three.mixed
octic = mixed.octic
contraction = octic.prior.quintic
cubic = contraction.cubic
quartic = contraction.quart

SAMPLE_SIZE = 3000
SEED = 20261124


def stage_rows():
    """Rows of F_2 (the inherited rows of stage 3) and the six quartic rows."""
    old = [((width,) if width else (), profile, size)
           for width, profile, size in cubic.subgrid.linear]
    old.extend(((a, b), profile, size)
               for a, b, profile, size in cubic.subgrid.pairs)
    for widths, coefficients in cubic.CUBIC_ROWS:
        old.append(quartic.profile_row(widths, coefficients))
    extra = [quartic.profile_row((width,) * 4, coefficients)
             for width, coefficients in quartic.QUARTIC_ROWS]
    return old, extra


def legendre_row(widths, order):
    return quartic.profile_row(widths, [0] * (order // 2 - 1) + [1])


def main(sample_size=SAMPLE_SIZE):
    old, extra = stage_rows()
    stage3 = 0
    for i, row in enumerate(extra):
        for other in old + extra[:i + 1]:
            assert cubic.inner_product(row, other) == contraction.inner(row, other)
            stage3 += 1
    print(f"Stage 3: {stage3} Gram entries agree by partitions and by matchings.")

    f4 = old + extra + [quartic.profile_row(widths, coefficients)
                        for widths, coefficients in contraction.QUINTIC_ROWS]
    r6 = [legendre_row((width,) * degree, order)
          for degree, width, order, _ in octic.prior.PROFILES]
    r7 = [legendre_row(widths, order) for widths, order, _ in octic.PROFILES]
    new = [quartic.profile_row(widths, coefficients)
           for widths, coefficients in (*mixed.PROFILES.items(), *three.PROFILES.items())]
    mutual = 0
    for i, row in enumerate(new):
        for other in new[:i + 1]:
            assert partitions.partition_inner(row, other) == contraction.inner(row, other)
            mutual += 1
    print(f"Rows (R8)-(R9): {mutual} mutual Gram entries agree.")
    against = 0
    for row in new:
        for other in r6 + r7:
            assert partitions.partition_inner(row, other) == contraction.inner(row, other)
            against += 1
    print(f"Rows (R8)-(R9) against (R6)-(R7): {against} Gram entries agree.")
    indices = random.Random(SEED).sample(range(len(new) * len(f4)), sample_size)
    for index in indices:
        row, other = new[index // len(f4)], f4[index % len(f4)]
        assert partitions.partition_inner(row, other) == contraction.inner(row, other)
    print(f"Rows (R8)-(R9) against F_4: {len(indices)} distinct sampled Gram entries "
          f"agree (seed {SEED}; {len(new)} x {len(f4)} entries in all).")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else SAMPLE_SIZE)
