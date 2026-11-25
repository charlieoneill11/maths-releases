// Build with g++ -O3 -std=c++17 fast_power_witness.cpp -lgmpxx -lgmp -o fast_power_witness
// Usage: fast_power_witness FIRST LAST [--witnesses] [--gmp-check].
// Add -DPOWER_WITNESS_SQUARES for strict consecutive-square intervals.
#ifndef POWER_WITNESS_SCALAR
#include <immintrin.h>
#endif
#include <gmpxx.h>
#include <algorithm>
#include <array>
#include <charconv>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

using Integer = mpz_class;
using U64 = uint64_t;
using U128 = unsigned __int128;
constexpr U128 montgomery_R=U128(1)<<104;
constexpr U64 group_size = 8192;
#ifdef POWER_WITNESS_SCALAR
constexpr unsigned lanes_count = 4;
constexpr const char* program_name = "portable_power_witness";
constexpr const char* backend_name = "scalar";
constexpr const char* batch_name = "scalar batches";
#else
using Vec = __m512i;
constexpr U64 mask52=(U64(1)<<52)-1;
constexpr unsigned vectors = 5;
constexpr unsigned lanes_count = 8 * vectors;
constexpr const char* program_name = "fast_power_witness";
constexpr const char* backend_name = "SIMD";
constexpr const char* batch_name = "vector batches";
#endif

Integer floor_power(U64 n) {
    static_assert(sizeof(unsigned long) >= sizeof(U64), "64-bit GMP required");
    Integer power(static_cast<unsigned long>(n));
#ifdef POWER_WITNESS_SQUARES
    mpz_mul(power.get_mpz_t(), power.get_mpz_t(), power.get_mpz_t());
#else
    mpz_pow_ui(power.get_mpz_t(), power.get_mpz_t(), 11);
    mpz_root(power.get_mpz_t(), power.get_mpz_t(), 5);
#endif
    return power;
}

bool gmp_euler_check(const Integer& p) {
    Integer result, base = 3, exponent = (p-1)/2;
    mpz_powm(result.get_mpz_t(), base.get_mpz_t(), exponent.get_mpz_t(), p.get_mpz_t());
    return result == p-1;
}


U128 native(const Integer& n) {
    size_t used=0;
    U128 out=0;
    if (n<0 || mpz_sizeinbase(n.get_mpz_t(),2)>128) throw std::runtime_error("128-bit bound");
    mpz_export(&out,&used,-1,sizeof(U128),0,0,n.get_mpz_t());
    return out;
}
Integer big(U128 n) {
    Integer out;
    mpz_import(out.get_mpz_t(),1,-1,sizeof(n),0,0,&n);
    return out;
}
unsigned bits(U128 n) {
    U64 top=n>>64;
    return top?128-__builtin_clzll(top):64-__builtin_clzll(static_cast<U64>(n));
}
#ifdef POWER_WITNESS_SCALAR
#include "scalar_power_euler.hpp"
#else
#pragma GCC push_options
#pragma GCC target("avx512f,avx512dq,avx512ifma")
struct Pair { Vec lo,hi; };
inline Vec add(Vec a,Vec b) {return _mm512_add_epi64(a,b);}
inline Vec low(Vec a) {return _mm512_and_si512(a,_mm512_set1_epi64(mask52));}
inline Vec upper(Vec a) {return _mm512_srli_epi64(a,52);}
inline Vec fmalo(Vec sum,Vec a,Vec b) {return _mm512_madd52lo_epu64(sum,a,b);}
inline Vec fmahi(Vec sum,Vec a,Vec b) {return _mm512_madd52hi_epu64(sum,a,b);}

// Radix-2^52 schoolbook square, followed by two Montgomery cancellation steps.
inline Pair square(Pair x,Pair n,Vec inverse) {
    const Vec zero=_mm512_setzero_si512();
    Vec t0=fmalo(zero,x.lo,x.lo);
    Vec cross_lo=fmalo(zero,x.lo,x.hi), cross_hi=fmahi(zero,x.lo,x.hi);
    Vec t1=fmahi(add(cross_lo,cross_lo),x.lo,x.lo);
    Vec t2=fmalo(add(cross_hi,cross_hi),x.hi,x.hi);
    Vec t3=fmahi(zero,x.hi,x.hi);
    Vec q0=fmalo(zero,t0,inverse);
    t0=fmalo(t0,q0,n.lo);
    t1=fmahi(add(t1,upper(t0)),q0,n.lo);
    t1=fmalo(t1,q0,n.hi);
    t2=fmahi(t2,q0,n.hi);
    Vec q1=fmalo(zero,t1,inverse);
    t1=fmalo(t1,q1,n.lo);
    t2=fmahi(add(t2,upper(t1)),q1,n.lo);
    t2=fmalo(t2,q1,n.hi);
    t3=fmahi(t3,q1,n.hi);
    return {low(t2),add(t3,upper(t2))};
}
inline Pair times_three(Pair x,__mmask8 selected) {
    Vec lo=add(x.lo,add(x.lo,x.lo));
    Vec hi=add(x.hi,add(x.hi,x.hi));
    return {_mm512_mask_mov_epi64(x.lo,selected,low(lo)),
            _mm512_mask_mov_epi64(x.hi,selected,add(hi,upper(lo)))};
}

U64 euler_batch(const std::array<U128,lanes_count>& p,unsigned bit_count,unsigned two_bits) {
    Pair n[vectors],x[vectors];Vec inv[vectors],el[vectors],eh[vectors];
    alignas(64) U64 one_lo[lanes_count],one_hi[lanes_count];
    for(unsigned g=0;g<vectors;g++) {
        alignas(64) U64 nlo[8],nhi[8],elo[8],ehi[8];
        for(unsigned l=0;l<8;l++) {
            unsigned i=8*g+l;
            U128 one=montgomery_R%p[i],e=p[i]>>1;
            nlo[l]=p[i]&mask52;nhi[l]=p[i]>>52;
            one_lo[i]=one&mask52;one_hi[i]=one>>52;
            elo[l]=e;ehi[l]=e>>64;
        }
        n[g]={_mm512_load_si512(nlo),_mm512_load_si512(nhi)};
        x[g]={_mm512_load_si512(one_lo+8*g),_mm512_load_si512(one_hi+8*g)};
        inv[g]=low(_mm512_sub_epi64(n[g].lo,_mm512_set1_epi64(2)));
        el[g]=_mm512_load_si512(elo);eh[g]=_mm512_load_si512(ehi);
    }
    for (int bit=static_cast<int>(bit_count)-2;bit>=static_cast<int>(two_bits)-1;--bit) {
        Vec test=_mm512_set1_epi64(U64(1)<<(bit%64));
        #pragma GCC unroll 8
        for(unsigned g=0;g<vectors;g++) {
            x[g]=square(x[g],n[g],inv[g]);
            x[g]=times_three(x[g],_mm512_test_epi64_mask(bit>=64?eh[g]:el[g],test));
        }
    }
    for (unsigned j=0;j<two_bits-1;j++) {
        #pragma GCC unroll 8
        for(unsigned g=0;g<vectors;g++) x[g]=square(x[g],n[g],inv[g]);
    }
    U64 ok=0;
    for(unsigned g=0;g<vectors;g++) {
        alignas(64) U64 out_lo[8],out_hi[8];
        _mm512_store_si512(out_lo,x[g].lo);_mm512_store_si512(out_hi,x[g].hi);
        for(unsigned l=0;l<8;l++) {
            unsigned i=g*8+l;
            U128 res=(U128(out_hi[l])<<52)+out_lo[l];
            U128 minus=p[i]-((U128(one_hi[i])<<52)+one_lo[i]);
            if(res==minus || res==minus+p[i]) ok|=U64(1)<<i;
        }
    }
    return ok;
}

#pragma GCC pop_options
#endif

struct PrimeSieve {
    unsigned prime, offset, high_mod[8];
    U64 inverse;
};
struct Sieve {
    std::vector<PrimeSieve> primes;
    std::vector<U64> masks;
    explicit Sieve(unsigned s) {
        constexpr unsigned limit = 401;
        for(unsigned p=5;p<=limit;p+=2) {
            bool prime=true;
            for(unsigned j=3;j*j<=p;j+=2)if(p%j==0){prime=false;break;}
            if(!prime)continue;
            PrimeSieve info{p,unsigned(masks.size()),{},UINT64_MAX/p};
            U64 hi=(U128(1)<<64)%p;
            for(unsigned j=0;j<8;j++)info.high_mod[j]=j*hi%p;
            primes.push_back(info);
            masks.resize(masks.size()+p,UINT64_MAX);
            U64 f=(U64(1)<<s)%p;
            unsigned root=1;
            while((f*root+1)%p)++root;
            for(unsigned j=0;j<64;j++) {
                masks[info.offset+(root+p-3*j%p)%p] &= ~(U64(1)<<j);
            }
        }
    }
    U64 bits(U128 start)const {
        U64 mask=UINT64_MAX, lo=start, hi=start>>64;
        for(const PrimeSieve& sieve:primes) {
            U64 q=(U128(lo)*sieve.inverse)>>64;
            unsigned r=lo-q*sieve.prime;
            if(r>=sieve.prime)r-=sieve.prime;
            r+=sieve.high_mod[hi];if(r>=sieve.prime)r-=sieve.prime;
            mask&=masks[sieve.offset+r];
        }
        return mask;
    }
};
struct Lane {U128 r=0,upper=0,p=0,block_start=0;U64 index=0,mask=0;bool alive=false;};
struct Band {
    U64 first,size; U128 lower,min_width,max_width,upper_guard;
    Band(U64 a,U64 b):first(a),size(b-a+1) {
        U128 next=native(floor_power(a+1));
        lower=native(floor_power(a));
        U128 last=native(floor_power(b+1));
        upper_guard=last;
        min_width=next-lower-1;
        max_width=native(floor_power(b+2))-last+1;
        if (min_width<=size*(max_width-min_width)+2)
            throw std::runtime_error("guard intervals too tight");
    }
};
void load_lane(Lane& x,const Band& b,U64 j,unsigned shift) {
    x.index=j;x.alive=true;x.mask=0;
    U128 guard=b.lower+1+j*b.max_width;
    x.upper=b.lower+(j+1)*b.min_width;
    x.r=(guard>>shift)+1;
    x.r+=((U64(1)<<shift)%3+3-x.r%3)%3;
}
U128 candidate(Lane& x,const Sieve& sieve,unsigned shift) {
    while(x.mask==0) {
        if((x.r<<shift)>=x.upper)return 0;
        x.block_start=x.r;x.mask=sieve.bits(x.r);x.r+=3*64;
    }
    unsigned j=__builtin_ctzll(x.mask); x.mask &= x.mask-1;
    x.p=((x.block_start+3*j)<<shift)+1;
    if(x.p>=x.upper)return 0;
    return x.p;
}
bool has_square_discriminant(U128 p,unsigned s) {
    U128 f=U128(1)<<s, r=(p-1)>>s, sum=r&(f-1), product=r>>s;
    if(sum*sum<4*product)return false;
    Integer disc=big(sum*sum-4*product);
    return mpz_perfect_square_p(disc.get_mpz_t());
}

U64 parse_bound(std::string_view text) {
    U64 value = 0;
    const char* end = text.data() + text.size();
    auto parsed = std::from_chars(text.data(), end, value);
    if (parsed.ec != std::errc() || parsed.ptr != end) {
        throw std::invalid_argument("invalid integer bound");
    }
    return value;
}

int run(int argc, char** argv) {
    if (argc < 3) {
        throw std::invalid_argument(std::string("usage: ") + program_name + " FIRST LAST [--witnesses] [--gmp-check]");
    }
    U64 first = parse_bound(argv[1]), last = parse_bound(argv[2]);
#ifdef POWER_WITNESS_SQUARES
    if (first < 70'500'000'000'000ULL || last > 734'000'000'000'000ULL || last < first)
        throw std::invalid_argument("bounds outside supported square range [70500000000000,734000000000000]");
#else
    if (first < 3800000000000ULL || last > 32700000000000ULL || last < first) {
        throw std::invalid_argument("bounds outside supported contiguous interval [3800000000000,32700000000000]");
    }
#endif
    bool emit = false, check = false;
    for (int i=3; i<argc; ++i) {
        std::string_view option = argv[i];
        if (option == "--witnesses") emit = true;
        else if (option == "--gmp-check") check = true;
        else throw std::invalid_argument("unknown option");
    }
#ifndef POWER_WITNESS_SCALAR
    if (!__builtin_cpu_supports("avx512f") || !__builtin_cpu_supports("avx512dq") ||
        !__builtin_cpu_supports("avx512ifma")) {
        throw std::runtime_error("AVX-512 IFMA unavailable; use verify_11_5.cpp");
    }
#endif

    auto started = std::chrono::steady_clock::now();
    U64 total = 0, batches = 0;
    std::optional<Sieve> sieve;
    unsigned previous_shift = 0;
    for (U64 a=first; a<=last; a+=group_size) {
        Band band(a,std::min(last,a+group_size-1));
        unsigned width = bits(band.upper_guard);
        unsigned shift = (width+2)/3;
        if (shift < 26 || band.upper_guard >= montgomery_R/36 ||
            (band.upper_guard >> shift) + 192 >= (U128(8) << 64)) {
            throw std::runtime_error("unsupported modulus or presieve quotient");
        }
        if (shift != previous_shift) {
            sieve.emplace(shift);
            previous_shift = shift;
        }

        std::array<Lane,lanes_count> lanes{};
        std::array<U128,lanes_count> samples{};
        std::vector<U128> witnesses(band.size);
        U64 next = 0, done = 0;
        while (done < band.size) {
            U128 fill = 0;
            for (unsigned l=0; l<lanes_count; ++l) {
                if (!lanes[l].alive && next < band.size) {
                    load_lane(lanes[l],band,next++,shift);
                }
                if (lanes[l].alive) {
                    samples[l] = candidate(lanes[l],*sieve,shift);
                    if (!samples[l]) {
                        throw std::runtime_error("no witness in the guarded subinterval at n=" +
                                                 std::to_string(a+lanes[l].index));
                    }
                    fill = samples[l];
                    ++total;
                }
            }
            // The final short vector borrows a valid modulus for unused lanes.
            for (unsigned l=0; l<lanes_count; ++l) {
                if (!lanes[l].alive) samples[l] = fill;
            }
            U64 ok = euler_batch(samples,width,shift);
            ++batches;
            for (unsigned l=0; l<lanes_count; ++l) {
                if (!lanes[l].alive || !((ok >> l) & 1)) continue;
                U128 p = samples[l];
                if (has_square_discriminant(p,shift)) continue;
                if (check && !gmp_euler_check(big(p))) {
                    throw std::runtime_error(std::string("GMP rejected a ") + backend_name + " witness");
                }
                witnesses[lanes[l].index] = p;
                lanes[l].alive = false;
                ++done;
            }
        }
        if (emit) {
            for (U64 i=0; i<band.size; ++i) {
                std::cout << a+i << ' ' << big(witnesses[i]) << '\n';
            }
            if (!std::cout) throw std::runtime_error("witness output failed");
        }
    }
    if (emit) {
        std::cout.flush();
        if (!std::cout) throw std::runtime_error("witness output failed");
    }
    std::chrono::duration<double> runtime = std::chrono::steady_clock::now()-started;
    std::cerr << "Witnesses " << last-first+1 << ", candidates " << total
              << ", " << batch_name << ' ' << batches << ", seconds " << runtime.count() << '\n';
    return 0;
}

int main(int argc, char** argv) {
    try {
        return run(argc,argv);
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
