"""Verify an IW witness archive using only Python's standard library."""
import argparse
import gzip
from math import isqrt
from pathlib import Path
from zlib import crc32


def prove(n, left, right, p):
    if p < 3 or p % 2 == 0 or not left < p**5 < right:
        raise ValueError(f'Interval or parity check failed at {n}')
    power = (p-1) & -(p-1)
    if power**3 <= p or pow(3,(p-1)//2,p) != p-1:
        raise ValueError(f'Primality certificate failed at {n}')
    if (power+1)**2 <= p:
        product, total = divmod((p-1)//power, power)
        discriminant = total**2 - 4*product
        if discriminant >= 0 and isqrt(discriminant)**2 == discriminant:
            raise ValueError(f'Possible composite at {n}')


class Reader:
    def __init__(self, stream):
        self.stream = stream
        self.crc = 0

    def read(self, length):
        data = self.stream.read(length)
        if len(data) != length:
            raise ValueError('Truncated archive')
        self.crc = crc32(data,self.crc)
        return data

    def integer(self, length):
        return int.from_bytes(self.read(length),'little')

    def residual(self):
        value = 0
        for shift in range(0,101,7):
            byte = self.integer(1)
            value |= (byte & 127) << shift
            if byte < 128:
                if (shift and byte == 0) or value >= 2**101:
                    raise ValueError('Invalid encoded residual')
                return value//2 if value%2 == 0 else -(value//2)-1
        raise ValueError('Overlong residual')


def read_block(reader, size):
    code = reader.integer(1)
    shift = code & 127
    if not 1 <= shift < 100:
        raise ValueError('Invalid stride')
    stride = (1 << shift)*(3 if code & 128 else 1)
    anchor = reader.integer(13)
    yield anchor
    if size == 1:
        return
    end = reader.integer(13)
    span, rem = divmod(end-anchor,stride)
    if rem or span <= 0:
        raise ValueError('Invalid block endpoints')
    for i in range(1,size-1):
        index = span*i//(size-1)+reader.residual()
        if not 0 < index < span:
            raise ValueError('Invalid block offset')
        yield anchor+index*stride
    yield end


def verify(first, last, path, square_summary=False):
    if not 0 < first <= last < 2**45:
        raise ValueError('Invalid expected endpoint')
    with gzip.open(path,'rb') as stream:
        reader = Reader(stream)
        if reader.read(8) != b'I11WIT\x01\x00' or reader.integer(8) != first:
            raise ValueError('Wrong format or starting base')
        n = first
        left = n**11
        square_first = square_last = None
        distinct_squares = 0
        while size := reader.integer(2):
            if size != min(2048,last+1-n):
                raise ValueError(f'Unexpected block length at {n}')
            for p in read_block(reader,size):
                right = (n+1)**11
                prove(n,left,right,p)
                if square_summary:
                    m = isqrt(p)
                    if not m*m < p < (m+1)**2:
                        raise ValueError(f'Square interval check failed for {n}')
                    if square_first is None:
                        square_first = m
                    if m != square_last:
                        distinct_squares += 1
                    square_last = m
                left = right
                n += 1
        if n != last+1 or reader.integer(8) != last-first+1:
            raise ValueError('Missing witnesses or wrong footer count')
        expected = reader.crc
        if reader.integer(4) != expected or stream.read(1):
            raise ValueError('Checksum or trailing data error')
    print(f'Verified all {last-first+1:,} witnesses for {first} through {last}.')
    if square_summary:
        print(f'Distinct square bases: {distinct_squares:,}, from {square_first:,} to {square_last:,}.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('first',type=int)
    parser.add_argument('last',type=int)
    parser.add_argument('archive',type=Path)
    parser.add_argument('--square-summary',action='store_true')
    args=parser.parse_args()
    verify(args.first,args.last,args.archive,args.square_summary)
