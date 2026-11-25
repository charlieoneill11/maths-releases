// Return every quadruple of local indices with sum of 64-bit keys equal to target.
// Unsigned wraparound implements the additive group Z/(2^64). The caller verifies
// the original integer coordinates for every returned quadruple.
#include <algorithm>
#include <array>
#include <cstdint>
#include <limits>
#include <vector>

namespace {
struct Entry {
    std::uint64_t sum;
    std::uint32_t x, y, next;
};
constexpr std::uint32_t none = std::numeric_limits<std::uint32_t>::max();

std::uint64_t scramble(std::uint64_t x) {
    x ^= x >> 30;
    x *= UINT64_C(0xbf58476d1ce4e5b9);
    x ^= x >> 27;
    return x * UINT64_C(0x94d049bb133111eb) ^ (x >> 31);
}
}

extern "C" std::int64_t join4(const std::uint64_t **keys, const std::uint32_t *sizes,
                              std::uint64_t target, std::uint32_t *out, std::uint64_t capacity) {
    try {
        std::array<int,4> order{0,1,2,3};
        std::sort(order.begin(), order.end(), [&](int x,int y){return sizes[x]<sizes[y];});
        int a=order[0], b=order[3], c=order[1], d=order[2];
        auto pairs = [&](int i,int j){return std::uint64_t(sizes[i])*sizes[j];};
        if (pairs(a,b)>pairs(c,d)) {std::swap(a,c); std::swap(b,d);}
        if (!sizes[a] || !sizes[b] || !sizes[c] || !sizes[d]) return 0;
        // Chunk the stored side to keep all work arrays comfortably in memory.
        std::uint32_t width=std::max<std::uint32_t>(1, 3000000U/sizes[b]);
        std::uint64_t found=0;
        for (std::uint32_t first=0;first<sizes[a];first+=width) {
            auto end=std::min(sizes[a],first+width);
            std::size_t n=std::size_t(end-first)*sizes[b];
            std::size_t slots=1;
            while (slots<n*2) slots*=2;
            std::vector<std::uint32_t> heads(slots,none);
            std::vector<Entry> list;
            list.reserve(n);
            for (auto i=first;i<end;++i) for (std::uint32_t j=0;j<sizes[b];++j) {
                auto sum=keys[a][i]+keys[b][j];
                auto slot=scramble(sum)&(slots-1);
                auto index=static_cast<std::uint32_t>(list.size());
                list.push_back({sum,i,j,heads[slot]});
                heads[slot]=index;
            }
            for (std::uint32_t k=0;k<sizes[c];++k) for (std::uint32_t l=0;l<sizes[d];++l) {
                auto wanted=target-keys[c][k]-keys[d][l];
                for (auto idx=heads[scramble(wanted)&(slots-1)];idx!=none;idx=list[idx].next) {
                    const auto &e=list[idx];
                    if (e.sum!=wanted) continue;
                    if (found<capacity) {
                        auto row=out+4*found;
                        row[a]=e.x; row[b]=e.y; row[c]=k; row[d]=l;
                    }
                    ++found;
                }
            }
        }
        return static_cast<std::int64_t>(found);
    } catch (...) {
        return -1;
    }
}
