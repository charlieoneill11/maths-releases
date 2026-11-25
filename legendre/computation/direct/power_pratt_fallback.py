#!/usr/bin/env python3
"""Generate or check a prime certificate for one open 11/5-power interval.

    python power_pratt_fallback.py generate N > proof.json
    python -S power_pratt_fallback.py verify proof.json --expected-base N

Generation needs SymPy. Verification uses only the Python standard library.
The proof lists [prime, generator, factors of prime minus one with repetition]
in increasing order of prime. All integers are decimal strings. The prime 2
is implicit. Exit 0 means certified, 1 means the search was inconclusive,
and 2 reports invalid input, an invalid certificate, or an I/O error.
"""
import argparse
import json
import sys
from math import prod
from pathlib import Path

FORMAT = "power-11-5-pratt-v1"


def positive(value):
    if not isinstance(value, str) or not value.isascii() or not value.isdigit() or value[0] == "0":
        raise ValueError("expected a positive integer in canonical decimal notation")
    return int(value)


def floor_fifth_root(value):
    root = 1 << ((value.bit_length() + 4) // 5)
    while True:
        following = (4 * root + value // root**4) // 5
        if following >= root:
            return root
        root = following


def verifies_order(p, generator, factors):
    return (1 < generator < p and pow(generator, p - 1, p) == 1
            and all(pow(generator, (p - 1) // q, p) != 1 for q in set(factors)))


def verify(n, certificate, *, square=False):
    if not isinstance(certificate, dict) or set(certificate) != {"format", "n", "p", "proof"}:
        raise ValueError("invalid certificate header")
    format_name = "square-pratt-v1" if square else FORMAT
    if certificate["format"] != format_name or positive(certificate["n"]) != n:
        raise ValueError("certificate format or requested interval does not match")
    p = positive(certificate["p"])
    endpoint_exp, prime_exp = (2, 1) if square else (11, 5)
    if not n**endpoint_exp < p**prime_exp < (n + 1)**endpoint_exp:
        raise ValueError("prime candidate is outside the strict interval")
    if not isinstance(certificate["proof"], list):
        raise ValueError("proof must be a list of Lucas certificates")
    proven = {2}
    previous = 2
    for row in certificate["proof"]:
        if not isinstance(row, list) or len(row) != 3 or not isinstance(row[2], list):
            raise ValueError("malformed proof row")
        prime, generator = positive(row[0]), positive(row[1])
        factors = [positive(s) for s in row[2]]
        if not previous < prime <= p or not all(q in proven for q in factors):
            raise ValueError("unordered prime or missing factor certificate")
        if prod(factors) != prime - 1 or not verifies_order(prime, generator, factors):
            raise ValueError(f"Lucas primality check failed for {prime}")
        # The displayed unit has order prime-1, so phi(prime) >= prime-1.
        proven.add(prime)
        previous = prime
    if previous != p:
        raise ValueError("missing certificate for the interval prime")
    return p


def generate(n, candidates, factor_limit, bases, *, square=False):
    from sympy import factorint, isprime

    left = (n*n if square else floor_fifth_root(n**11)) + 1
    right_power = (n + 1)**(2 if square else 11)
    candidate = 2 if left <= 2 else left | 1
    for _ in range(candidates):
        if candidate**(1 if square else 5) >= right_power:
            break
        records = {}

        def certify(p):
            if p == 2 or p in records:
                return True
            if not isprime(p):
                return False
            proposed = factorint(p - 1, limit=factor_limit)
            factors = [int(q) for q, exponent in proposed.items() for _ in range(exponent)]
            if prod(factors) != p - 1:
                return False
            generator = next((a for a in range(2, min(p, 2 + bases))
                              if verifies_order(p, a, factors)), None)
            if generator is None or not all(certify(q) for q in sorted(set(factors))):
                return False
            records[p] = [str(p), str(generator), [str(q) for q in sorted(factors)]]
            return True

        if certify(candidate):
            certificate = {"format": "square-pratt-v1" if square else FORMAT,
                           "n": str(n), "p": str(candidate),
                           "proof": [records[q] for q in sorted(records)]}
            verify(n, certificate, square=square)
            return certificate
        candidate = 3 if candidate == 2 else candidate + 2
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    actions = parser.add_subparsers(dest="action", required=True)
    search = actions.add_parser("generate", help="search one interval and write its JSON proof to stdout")
    search.add_argument("n", type=positive)
    search.add_argument("--candidates", type=positive, default=4096, help="maximum candidates tested (default 4096)")
    search.add_argument("--factor-limit", type=positive, default=20000, help="SymPy factorint effort limit (default 20000)")
    search.add_argument("--bases", type=positive, default=128, help="maximum generator trials per proof node (default 128)")
    check = actions.add_parser("verify", help="verify a saved JSON proof for the supplied n")
    check.add_argument("certificate", type=Path)
    check.add_argument("--expected-base", dest="n", type=positive, required=True, help="base the certificate must prove")
    args = parser.parse_args()
    if args.action == "generate":
        try:
            certificate = generate(args.n, args.candidates, args.factor_limit, args.bases)
        except ImportError as error:
            print(f"Inconclusive for n={args.n}: {error}. Generation needs SymPy.", file=sys.stderr)
            return 1
        if certificate is None:
            print(f"Inconclusive for n={args.n}: no certificate within the search limits. "
                  "The interval may still contain primes.", file=sys.stderr)
            return 1
        json.dump(certificate, sys.stdout, separators=(",", ":"))
        print()
    else:
        with args.certificate.open(encoding="utf-8") as stream:
            p = verify(args.n, json.load(stream))
        print(f"Verified prime {p} strictly inside the 11/5-power interval at n={args.n}.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print(f"Error: {error}", file=sys.stderr)
        sys.exit(2)
