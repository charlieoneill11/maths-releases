"""Generate mixed_row_certificates.json for mixed_row_checks.py.

Sections 2 and 5 of the checker read it.  For Section 5 the disjunction tree is walked
depth first and a certificate is stored at the first node whose partial system has one.

For each branch, look for nonnegative multipliers of its rows whose combination is
-gap (or -1).  Candidates come from a floating LP and are rounded to rationals;
every stored certificate is then checked in exact arithmetic here and again by
mixed_row_checks.py.  If rounding fails, an exact rational LP is used instead.
"""
import json
import sys
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import linprog
import sympy as sp
from sympy.solvers.simplex import lpmin, InfeasibleLPError

from mixed_row_checks import branch_systems, VNAMES, stage12_systems, s5_rows, S5_NAMES

KEYS = VNAMES + ['1']


def exact_ok(rows, lam, target):
    comb = {}
    for i, q in lam:
        for k, v in rows[i].items():
            comb[k] = comb.get(k, Fr(0)) + q*v
    return {k: v for k, v in comb.items() if v != 0} == target


def find(rows, target):
    A = np.array([[float(r.get(k, 0)) for r in rows] for k in KEYS])
    b = np.array([float(target.get(k, 0)) for k in KEYS])
    res = linprog(np.ones(len(rows)), A_eq=A, b_eq=b, bounds=(0, None), method='highs')
    if res.success:
        for den in (10**4, 10**6, 10**8):
            lam = [(i, Fr(float(a)).limit_denominator(den)) for i, a in enumerate(res.x) if a > 1e-12]
            lam = [(i, q) for i, q in lam if q > 0]
            if exact_ok(rows, lam, target):
                return lam
    # exact fallback
    ls = sp.symbols(f'l0:{len(rows)}', nonnegative=True)
    eqs = [sp.Eq(sum(sp.Rational(r.get(k, Fr(0)).numerator, r.get(k, Fr(0)).denominator)*l for r, l in zip(rows, ls)),
                 sp.Rational(target.get(k, Fr(0)).numerator, target.get(k, Fr(0)).denominator)) for k in KEYS]
    try:
        _, sol = lpmin(sum(ls), eqs + [l >= 0 for l in ls])
    except InfeasibleLPError:
        return None
    lam = [(i, Fr(int(sp.Rational(sol[l]).p), int(sp.Rational(sol[l]).q))) for i, l in enumerate(ls) if sol[l] != 0]
    return lam if exact_ok(rows, lam, target) else None


def find_keys(rows, keys):
    A = np.array([[float(r.get(k, 0)) for r in rows] for k in keys])
    for tname, target in (('-gap', {'gap': Fr(-1)}), ('-1', {'1': Fr(-1)})):
        b = np.array([float(target.get(k, 0)) for k in keys])
        res = linprog(np.ones(len(rows)), A_eq=A, b_eq=b, bounds=(0, None), method='highs')
        if not res.success:
            continue
        for den in (10**3, 10**4, 10**6, 10**8):
            lam = [(i, Fr(float(a)).limit_denominator(den)) for i, a in enumerate(res.x) if a > 1e-12]
            lam = [(i, q) for i, q in lam if q > 0]
            if exact_ok(rows, lam, target):
                return tname, lam
    return None, None


def tree_certificates():
    keys = S5_NAMES + ['1']
    out = {}
    for name, (hyp, levels) in stage12_systems().items():
        found = []

        def dfs(path):
            tname, lam = find_keys(s5_rows(hyp, levels, path), keys)
            if tname is not None:
                found.append([list(path), tname, [[i, str(q)] for i, q in lam]])
                return
            if len(path) == len(levels):
                print('NO CERTIFICATE', name, path)
                sys.exit(1)
            for c in range(len(levels[len(path)])):
                dfs(path + (c,))
        dfs(())
        out['tree ' + name] = found
        print(name, len(found), flush=True)
    return out


def main():
    out = {}
    for fixed in (False, True):
        for band, branches in branch_systems(fixed):
            out[band] = {}
            for label, rows in branches:
                for tname, target in (('-gap', {'gap': Fr(-1)}), ('-1', {'1': Fr(-1)})):
                    lam = find(rows, target)
                    if lam is not None:
                        out[band][label] = {'target': tname,
                                            'multipliers': [[i, str(q)] for i, q in lam]}
                        break
                else:
                    print('NO CERTIFICATE', band, label)
                    sys.exit(1)
            print(band, len(out[band]), flush=True)
    out.update(tree_certificates())
    with open('mixed_row_certificates.json', 'w') as fh:
        json.dump(out, fh, indent=0, sort_keys=True)


if __name__ == '__main__':
    main()
