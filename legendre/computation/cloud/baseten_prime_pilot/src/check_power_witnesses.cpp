// Independent replay of the canonical decimal n,p stream from verify_11_5.
// Build: c++ -O3 -std=c++17 check_power_witnesses.cpp -lcrypto -o check_witnesses
// GMP:   c++ -O3 -std=c++17 -DUSE_GMP check_power_witnesses.cpp -lgmpxx -lgmp -o check_witnesses_gmp
// Usage: ./check_witnesses FIRST LAST < witnesses.txt
// Add -DPOWER_WITNESS_SQUARES to verify m^2 < p < (m+1)^2 instead.
#ifdef USE_GMP
#include <gmpxx.h>
#else
#include <openssl/bn.h>
#endif
#include <charconv>
#include <cstdint>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>

using Wide = unsigned __int128;
#ifdef POWER_WITNESS_SQUARES
constexpr unsigned endpoint_power = 2, witness_power = 1, index_bits = 50;
#else
constexpr unsigned endpoint_power = 11, witness_power = 5, index_bits = 45;
#endif

uint64_t read_index(const std::string& input) {
    uint64_t value = 0;
    const auto parsed = std::from_chars(input.data(), input.data() + input.size(), value);
    if (parsed.ec != std::errc() || parsed.ptr != input.data() + input.size())
        throw std::runtime_error("invalid base index");
    return value;
}

bool square_discriminant(Wide disc, uint64_t f) {
    uint64_t lo = 0, hi = f;
    while (lo+1 < hi) {
        uint64_t mid = lo + (hi-lo)/2;
        if (Wide(mid)*mid <= disc) lo = mid;
        else hi = mid;
    }
    return Wide(lo)*lo == disc;
}

bool valid_factor_shape(const std::string& decimal) {
    Wide p = 0;
    for (char digit : decimal) p = 10*p + unsigned(digit-'0');
    if (p < 3 || !(p & 1) || p >= (Wide(1) << 100)) return false;
    const uint64_t high = p >> 64;
    const unsigned bits = high ? 128-__builtin_clzll(high) : 64-__builtin_clzll(static_cast<uint64_t>(p));
    const unsigned shift = (bits+2)/3;
    const uint64_t f = uint64_t(1) << shift;
    if ((p-1) & (f-1)) return false;
    if (Wide(f+1)*(f+1) > p) return true;
    // A composite passing the Euler test would have factors 1+af, 1+bf.
    // Since p<f^3, its remainder and quotient here would give a+b and ab.
    const Wide r = (p-1) >> shift;
    const uint64_t sum = r & (f-1);
    const Wide product = r >> shift;
    return Wide(sum)*sum < 4*product || !square_discriminant(Wide(sum)*sum-4*product, f);
}

#ifdef USE_GMP
class Proof {
    mpz_class modulus, exponent, residue, lower, upper, raised_witness;
    const mpz_class three = 3;

public:
    explicit Proof(uint64_t first) {
        static_assert(sizeof(unsigned long) >= sizeof(uint64_t), "64-bit GMP required");
        mpz_ui_pow_ui(lower.get_mpz_t(), first, endpoint_power);
    }

    bool verify(uint64_t n, const std::string& decimal) {
        if (mpz_set_str(modulus.get_mpz_t(), decimal.c_str(), 10)) return false;
        mpz_pow_ui(raised_witness.get_mpz_t(), modulus.get_mpz_t(), witness_power);
        mpz_ui_pow_ui(upper.get_mpz_t(), n+1, endpoint_power);
        if (lower >= raised_witness || raised_witness >= upper) return false;
        lower.swap(upper);
        mpz_fdiv_q_2exp(exponent.get_mpz_t(), modulus.get_mpz_t(), 1);
        mpz_powm(residue.get_mpz_t(), three.get_mpz_t(), exponent.get_mpz_t(), modulus.get_mpz_t());
        return residue+1 == modulus;
    }
};
#else
using BnPtr = std::unique_ptr<BIGNUM, decltype(&BN_free)>;
class Proof {
    std::unique_ptr<BN_CTX, decltype(&BN_CTX_free)> context{BN_CTX_new(), BN_CTX_free};
    BnPtr modulus{BN_new(), BN_free}, exponent{BN_new(), BN_free};
    BnPtr three{BN_new(), BN_free}, residue{BN_new(), BN_free};
    BnPtr first_power{BN_new(), BN_free}, next_power{BN_new(), BN_free}, raised_witness{BN_new(), BN_free};
    BnPtr base{BN_new(), BN_free}, endpoint_exp{BN_new(), BN_free}, witness_exp{BN_new(), BN_free};

    void raise_endpoint(BIGNUM* result, uint64_t n) {
        if (!BN_set_word(base.get(), n) || !BN_exp(result, base.get(), endpoint_exp.get(), context.get()))
            throw std::runtime_error("OpenSSL power failed");
    }

public:
    explicit Proof(uint64_t first) {
        static_assert(sizeof(BN_ULONG) >= sizeof(uint64_t), "64-bit OpenSSL required");
        if (!context || !modulus || !exponent || !three || !residue || !first_power || !next_power ||
            !raised_witness || !base || !endpoint_exp || !witness_exp || !BN_set_word(three.get(), 3) ||
            !BN_set_word(endpoint_exp.get(), endpoint_power) || !BN_set_word(witness_exp.get(), witness_power))
            throw std::runtime_error("OpenSSL initialization failed");
        raise_endpoint(first_power.get(), first);
    }

    bool verify(uint64_t n, const std::string& decimal) {
        BIGNUM* existing = modulus.get();
        if (!BN_dec2bn(&existing, decimal.c_str()) || existing != modulus.get() ||
            !BN_exp(raised_witness.get(), modulus.get(), witness_exp.get(), context.get()))
            throw std::runtime_error("OpenSSL parsing or power failed");
        raise_endpoint(next_power.get(), n+1);
        if (BN_cmp(first_power.get(), raised_witness.get()) >= 0 || BN_cmp(raised_witness.get(), next_power.get()) >= 0)
            return false;
        first_power.swap(next_power);

        if (!BN_rshift1(exponent.get(), modulus.get()) ||
            !BN_mod_exp_mont(residue.get(), three.get(), exponent.get(), modulus.get(), context.get(), nullptr) ||
            !BN_add_word(residue.get(), 1))
            throw std::runtime_error("OpenSSL modular exponentiation failed");
        return BN_cmp(residue.get(), modulus.get()) == 0;
    }
};
#endif

int main(int argc, char** argv) try {
    if (argc != 3) throw std::runtime_error("usage: check_witnesses FIRST LAST < witnesses.txt");
    const uint64_t first = read_index(argv[1]), last = read_index(argv[2]);
    if (first == 0 || last < first || last >= (uint64_t(1) << index_bits))
        throw std::runtime_error("unsupported base range");
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);
    Proof proof(first);
    for (uint64_t n = first; n <= last; ++n) {
        std::string index, decimal;
        if (!(std::cin >> index >> decimal) || read_index(index) != n || decimal.empty() ||
            decimal.size() > 31 || decimal.front() == '0' || decimal.find_first_not_of("0123456789") != std::string::npos)
            throw std::runtime_error("missing or invalid record at " + std::to_string(n));
        if (!valid_factor_shape(decimal) || !proof.verify(n, decimal))
            throw std::runtime_error("invalid witness at " + std::to_string(n));
    }
    std::string extra;
    if (std::cin >> extra || std::cin.bad()) throw std::runtime_error("extra data or input error");
    std::cout << "Verified " << last-first+1 << " consecutive strict intervals and prime certificates.\n";
    return 0;
} catch (const std::exception& e) {
    std::cerr << e.what() << '\n';
    return 1;
}
