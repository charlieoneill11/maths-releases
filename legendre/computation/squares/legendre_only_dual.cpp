// Build with g++ -O3 -std=c++17 verify_11_5.cpp -lgmpxx -lgmp -o verify_11_5
// Usage: ./verify_11_5 FIRST LAST [--squares] [--witnesses]  (both bounds inclusive)
// The default tests 11/5 powers; --squares tests both strict Oppermann half-intervals.
#include <gmpxx.h>
#include <chrono>
#include <iostream>
#include <stdexcept>
#include <string>

using Integer = mpz_class;

Integer floor_power(const Integer& n) {
    Integer value;
    mpz_pow_ui(value.get_mpz_t(), n.get_mpz_t(), 11);
    mpz_root(value.get_mpz_t(), value.get_mpz_t(), 5);
    return value;
}

bool proves_prime(const Integer& p, const Integer& f) {
    // This routine requires p == 1 mod f, f a power of two, and p < f^3.
    // The Euler test forces every prime divisor of p to equal 1 mod f.
    // If p factors as (af+1)(bf+1), then s=a+b < f, ab=(r-s)/f,
    // where r=(p-1)/f. Hence the discriminant s^2-4ab must be a square.
    Integer r = (p - 1) / f;
    Integer s = r % f;
    Integer disc = s*s - 4*((r-s)/f);
    if (disc >= 0 && mpz_perfect_square_p(disc.get_mpz_t())) return false;

    Integer base = 3, exponent = (p-1)/2, residue;
    mpz_powm(residue.get_mpz_t(), base.get_mpz_t(), exponent.get_mpz_t(), p.get_mpz_t());
    return residue == p-1;
}

Integer find_witness(const Integer& lower_floor, const Integer& upper_floor) {
    // Excluding the upper floor costs at most one candidate and guarantees strictness.
    unsigned long bits = mpz_sizeinbase(upper_floor.get_mpz_t(), 2);
    Integer f = Integer(1) << ((bits + 2) / 3);
    Integer p = ((lower_floor + f - 1) / f)*f + 1;
    // Restrict to p = 5 mod 12. For such primes, 3 is a quadratic nonresidue.
    while (p % 3 != 2) p += f;
    Integer step = 3*f;
    constexpr unsigned long small_primes = 307444891294245705UL; // product of odd primes 3..47
    for (; p < upper_floor; p += step) {
        if (mpz_gcd_ui(nullptr, p.get_mpz_t(), small_primes) != 1) continue;
        if (proves_prime(p, f)) return p;
    }
    return 0;
}

int main(int argc, char** argv) {
    if (argc < 3) {
        std::cerr << "Usage: verify_11_5 FIRST LAST [--squares] [--witnesses]\n";
        return 2;
    }
    bool squares = false, witnesses = false;
    for (int i = 3; i < argc; ++i) {
        std::string option(argv[i]);
        if (option == "--squares") squares = true;
        else if (option == "--witnesses") witnesses = true;
        else return 2;
    }
    Integer first(argv[1], 10), last(argv[2], 10);
    if (first < 100 || last < first) return 2;
    Integer lower = squares ? Integer(first*first) : floor_power(first);
    auto started = std::chrono::steady_clock::now();
    for (Integer n = first; n <= last; ++n) {
        Integer upper, p, q;
        if (squares) {
            Integer middle = lower + n;
            upper = middle + n + 1;
            p = find_witness(lower, upper);
        } else {
            upper = floor_power(n+1);
            p = find_witness(lower, upper);
        }
        if (p == 0) {
            std::cerr << "No certificate found for n=" << n << '\n';
            return 1;
        }
        if (witnesses) {
            std::cout << n << ' ' << p;
            std::cout << '\n';
        }
        lower.swap(upper);
    }
    std::chrono::duration<double> seconds = std::chrono::steady_clock::now() - started;
    std::cerr << "Certified every n in [" << first << ", " << last << "] in "
              << seconds.count() << " seconds\n";
}
