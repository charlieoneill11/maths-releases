"""Check an Oppermann witness stream from verify_11_5 --squares --witnesses.

Run with python3 check_square_witnesses.py FIRST LAST < witnesses.txt.
Or append the .gz certificate path to check the compact stored witnesses.
All bounds are inclusive. The summary includes the SHA-256 digest of the stream.
"""
import gzip
from hashlib import sha256
from math import isqrt
import struct
import sys


def proves_prime(p):
    if p <= 3 or p % 2 == 0:
        return False
    f = (p - 1) & (1 - p)  # largest power of two dividing p-1
    if f**3 <= p or pow(3, (p - 1) // 2, p) != p - 1:
        return False
    if (f + 1)**2 > p:
        return True
    product, total = divmod((p - 1) // f, f)
    discriminant = total**2 - 4*product
    return discriminant < 0 or isqrt(discriminant)**2 != discriminant


def check(first, last, stream):
    if last < first:
        raise ValueError('Empty range')
    expected = first
    digest = sha256()
    for line in stream:
        n, p, q = map(int, line.split())
        if n != expected or not n*n < p < n*(n+1) < q < (n+1)**2:
            raise ValueError(f'Incorrect row or interval for n={n}')
        if not proves_prime(p) or not proves_prime(q):
            raise ValueError(f'Invalid prime certificate for n={n}')
        digest.update(line)
        expected += 1
    if expected != last + 1:
        raise ValueError(f'Expected stream to end after {last}, reached {expected-1}')
    print(f'Checked {last-first+1} indices in [{first}, {last}], two primes per index.')
    print('Witness SHA-256', digest.hexdigest())


def unpack_witness(lower, upper, offset):
    f = 1 << ((upper.bit_length() + 2) // 3)
    return (lower // f + offset)*f + 1


def unpack_rows(first, stream):
    n = first
    while pair := stream.read(4):
        left, right = struct.unpack('<HH', pair)
        middle = n*(n+1)
        p = unpack_witness(n*n, middle, left)
        q = unpack_witness(middle, (n+1)**2, right)
        yield f'{n} {p} {q}\n'.encode('ascii')
        n += 1


if __name__ == '__main__':
    first, last = map(int, sys.argv[1:3])
    if len(sys.argv) == 4:
        with gzip.open(sys.argv[3], 'rb') as certificate:
            check(first, last, unpack_rows(first, certificate))
    elif len(sys.argv) == 3:
        check(first, last, sys.stdin.buffer)
    else:
        raise SystemExit('Usage: check_square_witnesses.py FIRST LAST [CERTIFICATE.gz]')
