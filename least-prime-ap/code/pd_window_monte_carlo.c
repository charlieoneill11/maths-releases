/*
 * Monte Carlo estimates of the density h(alpha, beta) of integers n having a
 * divisor in [n^alpha, n^beta], in the Poisson--Dirichlet model.
 *
 * Heuristic cross-check only: no theorem of the paper uses this program.
 *
 * Model. As n runs over [1, x], the vector (log p / log n) over the prime
 * factors p of n, counted with multiplicity, converges in distribution to the
 * Poisson--Dirichlet(1) law (Billingsley). In that model h(alpha, beta) is the
 * probability that some sub-sum of the atoms lies in [alpha, beta]. Atoms are
 * drawn by stick-breaking (GEM(1)).
 *
 * Exact decision rule for one sample. Let w = beta - alpha. Call atoms of size
 * at least w "big" and the rest "small". Adding small atoms one at a time
 * cannot jump over an interval of length w. So a sub-sum lies in [alpha, beta]
 * exactly when some set S of big atoms has
 *     sum(S) <= beta  and  sum(S) + (total small mass) >= alpha.
 * Stick-breaking stops once the unbroken mass R falls below a threshold that
 * is smaller than w; R then consists only of atoms smaller than w, so it is
 * counted as small mass. No other approximation is made.
 *
 * Usage:
 *   pd_window_monte_carlo N SEED alpha1 beta1 [alpha2 beta2 ...]
 *       estimate h on each window from N samples
 *   pd_window_monte_carlo N SEED c
 *       estimate c = 1 - int_0^{1/2} h(alpha, 1/2) d alpha
 *       (the constant of Drappeau--Mounier, Corollary 1.3)
 *
 * Build: gcc -O2 -o pd_window_monte_carlo pd_window_monte_carlo.c -lm
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXATOMS 4096

static uint64_t st[2];
static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static inline uint64_t next64(void) { /* xoroshiro128+ */
    uint64_t s0 = st[0], s1 = st[1], r = s0 + s1;
    s1 ^= s0;
    st[0] = rotl(s0, 24) ^ s1 ^ (s1 << 16);
    st[1] = rotl(s1, 37);
    return r;
}
static inline double unif(void) { /* uniform on (0,1) */
    return ((double)(next64() >> 11) + 0.5) * (1.0 / 9007199254740992.0);
}
static void seed_rng(uint64_t seed) {
    uint64_t z = seed + 0x9E3779B97F4A7C15ULL; /* splitmix64 */
    for (int i = 0; i < 2; i++) {
        z += 0x9E3779B97F4A7C15ULL;
        uint64_t y = z;
        y = (y ^ (y >> 30)) * 0xBF58476D1CE4E5B9ULL;
        y = (y ^ (y >> 27)) * 0x94D049BB133111EBULL;
        st[i] = y ^ (y >> 31);
    }
}

/* Is there a set S of big[i..] with sum + sum(S) <= b and sum + sum(S) + small >= a? */
static int hit(const double *big, int nb, int i, double sum, double small, double a, double b) {
    if (sum > b) return 0;
    if (sum + small >= a) return 1;
    for (int j = i; j < nb; j++)
        if (hit(big, nb, j + 1, sum + big[j], small, a, b)) return 1;
    return 0;
}

/* One sample: does some sub-sum lie in [a, b]? */
static int sample(double a, double b) {
    double atoms[MAXATOMS], big[MAXATOMS];
    double w = b - a, thr = w < 2e-3 ? 0.5 * w : 1e-3, R = 1.0, small;
    int na = 0, nb = 0;
    while (R > thr) {
        if (na == MAXATOMS) { fprintf(stderr, "too many atoms\n"); exit(2); }
        double v = unif();
        atoms[na++] = R * v;
        R *= 1.0 - v;
    }
    small = R; /* the unbroken mass consists of atoms smaller than thr < w */
    for (int i = 0; i < na; i++) {
        if (atoms[i] >= w) big[nb++] = atoms[i];
        else small += atoms[i];
    }
    return hit(big, nb, 0, 0.0, small, a, b);
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: %s N SEED (alpha beta)... | c\n", argv[0]);
        return 2;
    }
    long N = atol(argv[1]);
    seed_rng(strtoull(argv[2], NULL, 10));
    if (N <= 0) return 2;
    if (strcmp(argv[3], "c") == 0) {
        long cnt = 0;
        for (long t = 0; t < N; t++) cnt += sample(0.5 * unif(), 0.5);
        double m = (double)cnt / N;
        printf("c = %.6f  (standard error %.6f)\n", 1.0 - 0.5 * m, 0.5 * sqrt(m * (1 - m) / N));
        return 0;
    }
    if ((argc - 3) % 2) return 2;
    for (int k = 3; k + 1 < argc; k += 2) {
        double a = atof(argv[k]), b = atof(argv[k + 1]);
        if (!(0 < a && a < b && b < 1)) return 2;
        long cnt = 0;
        for (long t = 0; t < N; t++) cnt += sample(a, b);
        double p = (double)cnt / N;
        printf("h(%.6f, %.6f) = %.6f  (standard error %.6f)\n", a, b, p, sqrt(p * (1 - p) / N));
    }
    return 0;
}
