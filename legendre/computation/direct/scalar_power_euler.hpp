// Independent scalar exponentiation backend. The caller supplies 83-99 bit odd moduli
// congruent to one modulo at least 2^26. GCC and Clang provide unsigned __int128.
#pragma once

struct ScalarModulus {
    U64 low;
    U64 high;
    U64 negative_inverse;
};

inline U128 scalar_montgomery_square(U128 x, const ScalarModulus& n) {
    const U64 low = static_cast<U64>(x);
    const U64 high = static_cast<U64>(x >> 64);
    const U128 low_square = U128(low) * low;
    const U64 digit0 = static_cast<U64>(low_square);
    const U64 cancel0 = digit0 * n.negative_inverse;

    // The two canceled low digits sum to zero modulo 2^64. Their carry is one
    // precisely when the original digit was nonzero.
    const U128 middle = 2 * U128(low) * high + U128(cancel0) * n.high
        + (low_square >> 64) + ((U128(cancel0) * n.low) >> 64) + (digit0 != 0);
    const U64 digit1 = static_cast<U64>(middle);
    const U64 cancel1 = digit1 * n.negative_inverse;

    return U128(high) * high + (middle >> 64) + ((U128(cancel1) * n.low) >> 64)
         + U128(cancel1) * n.high + (digit1 != 0);
}

U64 euler_batch(const std::array<U128,lanes_count>& moduli, unsigned bit_count,
                unsigned two_bits) {
    constexpr U64 powers_of_three[] = {1, 3, 9, 27, 81, 243, 729, 2187};
    // From the bottom of the nonzero part, group the exponent bits in triples.
    // The high group can have one, two, or three bits.
    const int top_window = two_bits + 3 * ((bit_count - two_bits - 1) / 3);
    std::array<U128,lanes_count> residues, montgomery_ones;
    std::array<ScalarModulus,lanes_count> n;
    for (unsigned l=0; l<lanes_count; ++l) {
        const U128 p = moduli[l];
        const U64 low = static_cast<U64>(p);
        const U64 w = low - 1;
        // w^3 vanishes modulo 2^64. Expanding -(1+w)^(-1) gives -1+w-w^2.
        n[l] = {low, static_cast<U64>(p >> 64), w - 1 - w*w};
        // Odd p>1 cannot divide 2^128, so this representative is in [1,p).
        montgomery_ones[l] = (~U128(0) % p) + 1;
        const unsigned leading = static_cast<unsigned>(p >> top_window) & 7;
        residues[l] = montgomery_ones[l] * powers_of_three[leading];
    }

    // The shared guard gives 36p < 2^104, hence 4374^2 p < 2^128.
    // For x < 4374p each raw Montgomery square is < p + x^2/2^128 < 2p.
    // Tripling in windows multiplies by at most 2187, restoring x < 4374p.
    // Multiplication intermediates fit 128 bits: p < 2^99 and x < 2^112.
    for (int bit=top_window-3; bit>=static_cast<int>(two_bits); bit-=3) {
        for (unsigned step=0; step<3; ++step) {
            for (unsigned l=0; l<lanes_count; ++l) {
                residues[l] = scalar_montgomery_square(residues[l], n[l]);
            }
        }
        for (unsigned l=0; l<lanes_count; ++l) {
            const unsigned window = static_cast<unsigned>(moduli[l] >> bit) & 7;
            residues[l] *= powers_of_three[window];
        }
    }
    // (p-1)/2 ends in at least two_bits-1 zero bits.
    for (unsigned bit=1; bit<two_bits; ++bit) {
        for (unsigned l=0; l<lanes_count; ++l) {
            residues[l] = scalar_montgomery_square(residues[l], n[l]);
        }
    }

    U64 mask = 0;
    for (unsigned l=0; l<lanes_count; ++l) {
        const U128 minus_one = moduli[l] - montgomery_ones[l];
        if (residues[l]==minus_one || residues[l]==minus_one+moduli[l]) {
            mask |= U64(1) << l;
        }
    }
    return mask;
}
