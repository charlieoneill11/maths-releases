// Integer enclosures for angular moments of the cap16 partial wave.
#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <iostream>
#include <map>
#include <vector>
using namespace std;
using I = long long;
using W = __int128;
constexpr I S = 1000000000000LL, H = S / 2, Q = 10000000000LL;
constexpr int N = 131072, FREQ = 512, TD = 10000;
using Box = array<I, 4>;
using Pt = array<I, 2>;
I floorq(W a, W b) {
  assert(b > 0);
  return a >= 0 ? a / b : -((-a + b - 1) / b);
}
I ceilq(W a, W b) { return -floorq(-a, b); }
vector<Pt> L, R;
I U;
Pt at(const vector<Pt> &wall, I y) {
  auto p = lower_bound(wall.begin(), wall.end(), Pt{y, 0});
  if ((*p)[0] == y)
    return {(*p)[1], (*p)[1]};
  auto prev = p - 1;
  I step = (*p)[0] - (*prev)[0];
  W v = W((*p)[0] - y) * (*prev)[1] + W(y - (*prev)[0]) * (*p)[1];
  return {floorq(v, step), ceilq(v, step)};
}
int status(Box b, int color) {
  bool possible = false;
  // Master sources are in [0,1] x [0,1/4], and destinations within one.
  for (int m = -1; m <= 1; m++) {
    I x = b[0] - m * U, X = b[1] - m * U;
    if (color > 3) {
      I z = -X;
      X = -x;
      x = z;
    }
    if (X < 0 || x > S)
      continue;
    I y = b[2] - 3 * m * H / 2, Y = b[3] - 3 * m * H / 2;
    for (int j = floorq(y, H); j <= floorq(Y, H); j++) {
      if (1 + 3 * (color > 3) + ((-j % 3) + 3) % 3 != color)
        continue;
      I a = max(I(0), y - j * H), h = min(H, Y - j * H);
      if (a > h)
        continue;
      Pt l = at(L, a), ll = at(L, h), r = at(R, a), rr = at(R, h);
      I minL = min(l[0], ll[0]), maxL = max(l[1], ll[1]),
        minR = min(r[0], rr[0]), maxR = max(r[1], rr[1]);
      if (a <= H / 2 && H / 2 <= h) {
        minL = L[L.size() / 2][1];
        maxR = R[R.size() / 2][1];
      }
      if (x > maxL && X < minR && y > j * H && Y < (j + 1) * H)
        return 2;
      if (X >= minL && x <= maxR)
        possible = true;
    }
  }
  return possible;
}
vector<array<Box, 4>> rays(N + 1);
vector<I> anglo(N + 1), anghi(N + 1);
void precompute() {
  for (int i = 0; i <= N; i++) {
    I a = I(N) * N - I(i) * i, b = 2LL * N * i, d = I(N) * N + I(i) * i;
    array<Pt, 4> p = {Pt{a, b}, Pt{-b, a}, Pt{-a, -b}, Pt{b, -a}};
    for (int q = 0; q < 4; q++) {
      W x = W(p[q][0]) * S, y = W(p[q][1]) * S;
      rays[i][q] = {floorq(x, d), ceilq(x, d), floorq(y, d), ceilq(y, d)};
    }
    // Each angle difference is 2 atan(N/den), with a sub-tick cubic correction.
    if (i) {
      I den = I(N) * N + I(i - 1) * i;
      anglo[i] = anglo[i - 1] + floorq(2 * W(S) * N, den) - 1;
      anghi[i] = anghi[i - 1] + ceilq(2 * W(S) * N, den);
    }
  }
}
// A common signed step function, pointwise below the native-minus-alternate
// indicator.
struct Span {
  int q, i, j, sign;
};
void visit(Box b, int alt, int q, int i, int j, vector<Span> &sp) {
  auto a = rays[i][q], d = rays[j][q];
  Box hit = {b[0] + min(a[0], d[0]), b[1] + max(a[1], d[1]),
             b[2] + min(a[2], d[2]), b[3] + max(a[3], d[3])};
  int native = status(hit, 1), other = alt ? status(hit, alt) : 0;
  int sign;
  if (native == 2)
    sign = 1;
  else if (other == 2)
    sign = -1;
  else if (native == 0 && other == 0)
    sign = 0;
  else if (j == i + 1)
    sign = other ? -1 : 0;
  else {
    int k = (i + j) / 2;
    visit(b, alt, q, i, k, sp);
    visit(b, alt, q, k, j, sp);
    return;
  }
  if (!sign)
    return;
  if (!sp.empty() && sp.back().q == q && sp.back().sign == sign &&
      sp.back().j == i)
    sp.back().j = j;
  else
    sp.push_back({q, i, j, sign});
}
map<int, array<Pt, FREQ>> phases;
const array<Pt, FREQ> &powers(int q, int i) {
  int key = q * (N + 1) + i;
  auto [it, fresh] = phases.try_emplace(key);
  if (fresh) {
    auto r = rays[i][q];
    I x = r[0], y = r[2], a = S, b = 0;
    for (int k = 0; k < FREQ; k++) {
      // At harmonic k the complex-power error is at most 6k/S.
      I u = (W(a) * x - W(b) * y) / S, v = (W(a) * y + W(b) * x) / S;
      it->second[k] = {u, v};
      a = u;
      b = v;
    }
  }
  return it->second;
}
I root(W z) {
  I s = (I)sqrtl((long double)z);
  while (W(s) * s > z)
    --s;
  while (W(s + 1) * (s + 1) <= z)
    ++s;
  return s;
}
I scaled(I measure) {
  return floorq(W(measure) * Q * 10000000,
                2 * W(S) * (measure < 0 ? 31415926 : 31415927));
}
// Bucket each affine positive part by the first threshold at which it
// contributes.
struct Buckets {
  array<I, TD + 1> mean{}, moment{};
};
vector<Buckets> bands(FREQ);
vector<Pt> saturation;
int native_boxes = 0, harmonic_boxes = 0;
I total_area = 0;
void check(Box b, int alt) {
  I area = ((b[1] - b[0]) / 1000000) * ((b[3] - b[2]) / 1000000);
  assert((b[1] - b[0]) % 1000000 == 0 && (b[3] - b[2]) % 1000000 == 0);

  assert(0 <= b[0] && b[0] < b[1] && b[1] < S && 0 < b[2] && b[2] < b[3] &&
         b[3] < H / 2);
  if (status(b, 1) != 2)
    return;
  total_area += area;
  assert(total_area <
         300000000); // All area-weighted bucket sums fit in signed 64 bits.
  vector<Span> sp;
  for (int q = 0; q < 4; q++)
    visit(b, alt, q, 0, N, sp);
  // All angular lengths and ray coordinates use a denominator of S.
  I mean = 0;
  array<Pt, FREQ> accum{};
  for (auto p : sp) {
    if (p.sign > 0)
      mean += anglo[p.j] - anglo[p.i];
    else
      mean -= anghi[p.j] - anghi[p.i];
    if (alt) {
      auto &a = powers(p.q, p.i), &h = powers(p.q, p.j);
      for (int k = 0; k < FREQ; k++)
        for (int d = 0; d < 2; d++)
          accum[k][d] += p.sign * (h[k][d] - a[k][d]);
    }
  }
  I mu = scaled(mean);
  assert(-Q <= mu && mu <= Q);
  if (!alt) {
    saturation.push_back({area, mu});
    ++native_boxes;
    return;
  }
  ++harmonic_boxes;
  if (alt)
    for (int k = 0; k < FREQ; k++) {
      auto [x, y] = accum[k];
      I magnitude = root(W(x) * x + W(y) * y) / (k + 1);
      I h = scaled(max(I(0), magnitude - I(12 * sp.size())));
      assert(0 <= h && h <= Q);
      int first =
          mu > 0 ? 0 : (!h ? TD + 1 : min(I(TD + 1), (-mu) * TD / h + 1));
      if (first <= TD) {
        bands[k].mean[first] += area * mu;
        bands[k].moment[first] += area * h;
      }
    }
}
bool credit(I target, bool receipt) {
  int last = 0;
  for (int d = 1; d <= 160; d++) {
    W high = 0;
    for (auto [a, f] : saturation)
      high += W(a) * max(I(0), f * d - Q);
    // Complement of the exact native-only area credit, on a common denominator.
    W need = W(target) * (U / 2) * Q * TD * d - 4 * high * TD * S;
    if (need <= 0) {
      if (receipt)
        cout << "native " << d << "\n";
      return true;
    }
    // Test each Fejer order with its cumulative sum of squared thresholds.
    W sum = 0, weighted = 0;
    int proof = 0;
    for (int k = 1; k <= FREQ; k++) {
      const auto &band = bands[k - 1];
      int low = 0, h = TD;
      while (h > low) {
        int m = (h + low) / 2;
        W val = W(band.mean[m]) * TD + W(band.moment[m]) * m;
        if (2 * val * d * S >= need)
          h = m;
        else
          low = m + 1;
      }
      sum += W(h) * h;
      weighted += W(k) * h * h;
      W left = 2 * d * ((k + 1) * sum - weighted),
        right = W(k + 1 - d) * (k + 1) * TD * TD;
      if (left < right) {
        proof = k;
        break;
      }
    }
    if (!proof)
      return false;
    if (receipt && proof != last)
      cout << "degree " << d << " " << proof << "\n";
    last = proof;
  }
  return false;
}
int main() {
  int n;
  cin >> U;
  for (auto wall : {&L, &R}) {
    cin >> n;
    for (int i = 0; i < n; i++) {
      I y, x;
      cin >> y >> x;
      wall->push_back({y, x});
    }
  }
  precompute();
  int alt;
  Box b;
  while (cin >> alt >> b[0] >> b[1] >> b[2] >> b[3])
    check(b, alt);
  for (auto &band : bands)
    for (int t = 1; t <= TD; t++) {
      band.mean[t] += band.mean[t - 1];
      band.moment[t] += band.moment[t - 1];
    }
  I low = 0, high = 3000;
  while (high > low + 1) {
    I mid = (high + low) / 2;
    if (credit(mid, false))
      low = mid;
    else
      high = mid;
  }
  cout << "bound " << low << " " << harmonic_boxes << " " << native_boxes
       << "\n";
  assert(credit(low, true));
}
