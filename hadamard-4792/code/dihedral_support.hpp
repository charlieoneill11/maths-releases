// Binary support filters for dihedral Golay pairs in which both rows contain
// an imaginary and a reflection entry. Bit j is the coefficient of z^j.
#pragma once
#include <array>
#include <cstdint>
#include <vector>

namespace binary_support {
using Mask=std::uint32_t;
using Count=std::uint64_t;
inline Mask bit(int k) {return Mask(1)<<k;}
inline int degree(Mask x) {return 31-__builtin_clz(x);}
inline int pop(Mask x) {return __builtin_popcount(x);}
inline Mask reverse(Mask x,int width) {
    x=((x&0x55555555u)<<1)|((x>>1)&0x55555555u);
    x=((x&0x33333333u)<<2)|((x>>2)&0x33333333u);
    x=((x&0x0f0f0f0fu)<<4)|((x>>4)&0x0f0f0f0fu);
    x=(x<<24)|((x&0xff00u)<<8)|((x>>8)&0xff00u)|(x>>24);
    return x>>(32-width);
}
inline Mask product(Mask x,Mask y) {
    Mask z=0;
    for(;y;y&=y-1) z^=x<<__builtin_ctz(y);
    return z;
}
inline Mask gcd(Mask a,Mask b) {
    while(b) {
        while(a && degree(a)>=degree(b)) a^=b<<(degree(a)-degree(b));
        Mask t=b;b=a;a=t;
    }
    return a;
}
struct Row {Mask i,v;};
struct Multipliers {std::vector<Row> rows;};
struct Counts {Count reduced=0,rows=0,pairs=0;};
template<class Visit>
bool enumerate(int n,int L,Visit visit,Counts& counts) {
    const int w=n-L;
    std::vector<Mask> pal;
    for(Mask half=1;half<bit(L/2+1);++half)
        pal.push_back(half|reverse(half,L+1));
    const Mask all=bit(n)-1,split=bit(w/2)-1;
    std::vector<Multipliers> groups(bit(w/2));
    std::vector<int> active;
    for(auto u:pal) for(auto v:pal) {
        if(!((u|v)&1) || gcd(u,v)!=1) continue;
        ++counts.reduced;
        for(Mask p=1;p<bit(w);++p) {
            auto reversed=reverse(p,w);
            if(p>reversed) continue;  // replacing one row by its adjoint
            Mask i=product(u,p),s=product(v,p);
            if(i&s) continue;
            // The real order-23 norm is 46, never a sum of two squares.
            // At +/-1 both reflection coordinates therefore vanish.
            if(n==23 && ((pop(s&0x55555555u)&1)||(pop(s&0xaaaaaaaau)&1))) continue;
            auto cls=(p^reversed)&split;
            if(groups[cls].rows.empty()) active.push_back(cls);
            groups[cls].rows.push_back({i&all,s&all});
            ++counts.rows;
        }
        for(int cls:active) {
            const auto& rows=groups[cls].rows;
            counts.pairs+=Count(rows.size())*(rows.size()+1)/2;
            if(visit(rows)) return true;
            groups[cls].rows.clear();
        }
        active.clear();
    }
    return false;
}
}
