// Complementary dihedral pairs from one skew-adjoint Laurent polynomial W.
// W = i + s*sum c_d (z^{-d}-z^d). The non-real parts are z^p W and
// (z^q + e z^{q+j}) W. Real letters fill every remaining position.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <unordered_map>
#include <vector>

namespace {
using Word=std::uint64_t;
using Mask=std::uint32_t;
constexpr int n=23;
constexpr Mask all=(1u<<n)-1, odd=0x2aaaaa;
using Poly=std::array<int,n>;
struct ARecord {int p; Mask negative;};
struct Key {Word h; int sum, alternating;};
struct SameKey {
    bool operator()(const Key& a,const Key& b) const {
        return a.h==b.h && a.sum==b.sum && a.alternating==b.alternating;
    }
};
struct HashKey {
    std::size_t operator()(const Key& x) const {
        return x.h^(Word(x.sum)<<23)^(Word(x.alternating)<<44);
    }
};
Word weights[2][n];
Word next_word(Word& x) {
    Word a=(x+=UINT64_C(0x9e3779b97f4a7c15));
    a=(a^(a>>30))*UINT64_C(0xbf58476d1ce4e5b9);
    a=(a^(a>>27))*UINT64_C(0x94d049bb133111eb);
    return a^(a>>31);
}
int pop(Mask x) {return __builtin_popcount(x);}
struct RealPart {
    Mask support;
    Mask paired[n]{};
    int pairs[n]{};
    Word linear[n]{};
    RealPart(Mask where,const Poly& shift):support(where) {
        for(int k=1;k<n;++k) {
            paired[k]=support&(support>>k); pairs[k]=pop(paired[k]);
            for(int h=0;h<n;++h) if(shift[h]) {
                if(h+k<n) linear[h+k]+=Word(shift[h])*weights[1][k];
                if(h>=k) linear[h-k]-=Word(shift[h])*weights[1][k];
            }
        }
    }
    Word hash(Mask neg) const {
        Word ans=0;
        for(int k=1;k<n;++k)
            ans+=weights[0][k]*Word(pairs[k]-2*pop((neg^(neg>>k))&paired[k]));
        for(Mask x=support;x;x&=x-1) {
            int j=__builtin_ctz(x);
            ans+=(neg&(1u<<j))?-linear[j]:linear[j];
        }
        return ans;
    }
    int sum(Mask neg) const {return pop(support)-2*pop(neg);}
    int alternating(Mask neg) const {return sum(neg^(support&odd));}
};
int autoc(const Poly& p,int k) {
    int v=0; for(int j=k;j<n;++j) v+=p[j]*p[j-k]; return v;
}
Word fixed_hash(const Poly& i,const Poly& s) {
    Word h=0;
    for(int k=1;k<n;++k) h+=weights[0][k]*Word(autoc(i,k)+autoc(s,k));
    return h;
}
Mask support(const Poly& i,const Poly& s) {
    Mask m=0;
    for(int j=0;j<n;++j) if(i[j]||s[j]) m|=1u<<j;
    return m;
}
bool exact(const Poly& ia,const Poly& sa,const Poly& ib,const Poly& sb,
           const Poly& pa,const Poly& pb,Mask na,Mask nb) {
    Poly a{},b{};
    for(int j=0;j<n;++j) {
        if(!ia[j] && !sa[j]) a[j]=(na>>j&1)?-1:1;
        if(!ib[j] && !sb[j]) b[j]=(nb>>j&1)?-1:1;
    }
    for(int k=1;k<n;++k) {
        if(autoc(a,k)+autoc(b,k)+autoc(ia,k)+autoc(ib,k)+autoc(sa,k)+autoc(sb,k)) return false;
        int anti=0;
        for(int j=k;j<n;++j)
            anti+=a[j]*pa[j-k]-a[j-k]*pa[j]+b[j]*pb[j-k]-b[j-k]*pb[j];
        if(anti) return false;
    }
    auto emit=[](const Poly& r,const Poly& i,const Poly& s) {
        for(int j=0;j<n;++j) std::cout<<(r[j]?r[j]:i[j]?2*i[j]:3*s[j])<<' ';
        std::cout<<'\n';
    };
    emit(a,ia,sa); emit(b,ib,sb);
    return true;
}
struct Counts {Word templates=0, a=0,b=0, overlaps=0;};
bool search(const std::vector<int>& offsets,const std::vector<int>& signs,Counts& count) {
    const int d=offsets.back();
    auto single=[&](int p) {
        Poly s{};
        for(unsigned k=0;k<offsets.size();++k) {
            s[p-offsets[k]]=signs[k]; s[p+offsets[k]]=-signs[k];
        }
        return s;
    };
    std::unordered_multimap<Key,ARecord,HashKey,SameKey> records;
    for(int p=d;p<n-d;++p) {
        Poly ia{}; ia[p]=1;
        auto sa=single(p);
        RealPart r(all^support(ia,sa),ia);
        auto base=fixed_hash(ia,sa);
        for(Mask neg=r.support;;neg=(neg-1)&r.support) {
            int sum=r.sum(neg),alt=std::abs(r.alternating(neg));
            // Simultaneously negating both real parts preserves every equation.
            if((sum==4||sum==6) && (alt==4||alt==6)) {
                records.emplace(Key{base+r.hash(neg),sum,alt},ARecord{p,neg});
                ++count.a;
            }
            if(!neg) break;
        }
    }
    for(int q=d;q<n-d;++q) for(int j=1;q+j<n-d;++j) for(int e:{-1,1}) {
        auto s0=single(q),s1=single(q+j);
        Poly p0{},p1{},ib{},sb{};
        p0[q]=1;p1[q+j]=1;
        if(support(p0,s0)&support(p1,s1)) continue;
        ++count.templates;
        for(int k=0;k<n;++k) {ib[k]=p0[k]+e*p1[k];sb[k]=s0[k]+e*s1[k];}
        RealPart r(all^support(ib,sb),ib);
        Word base=fixed_hash(ib,sb);
        int alt_e=(j%2)?-e:e;
        int required_b=e==1?5:3, required_alt_b=alt_e==1?5:3;
        for(Mask neg=r.support;;neg=(neg-1)&r.support) {
            if(std::abs(r.sum(neg))==required_b && std::abs(r.alternating(neg))==required_alt_b) {
                ++count.b;
                auto range=records.equal_range({0-base-r.hash(neg),e==1?4:6,alt_e==1?4:6});
                for(auto it=range.first;it!=range.second;++it) {
                    ++count.overlaps;
                    auto a=it->second;
                    Poly ia{};ia[a.p]=1;
                    if(exact(ia,single(a.p),ib,sb,ia,ib,a.negative,neg)) return true;
                }
            }
            if(!neg) break;
        }
    }
    return false;
}
}
int main(int argc,char** argv) {
    if(argc!=2) {std::cerr<<"usage: dihedral23 NUMBER_OF_OFFSET_PAIRS (1 through 4)\n";return 2;}
    int size=std::atoi(argv[1]);
    if(size<1 || size>4) return 2;
    Word seed=23;
    for(auto&set:weights) for(auto&v:set) v=next_word(seed);
    Counts count;
    // d=11 leaves only one center and cannot accommodate two copies.
    for(Mask chosen=1;chosen<(1u<<10);++chosen) if(pop(chosen)==size) {
        std::vector<int> offsets;
        for(int d=1;d<=10;++d) if(chosen>>(d-1)&1) offsets.push_back(d);
        for(int k=0;k<(1<<(size-1));++k) {
            std::vector<int> signs(size,1);
            for(int j=1;j<size;++j) signs[j]=(k>>(j-1)&1)?-1:1;
            if(search(offsets,signs,count)) {std::cout<<"DCS hit\n"; return 0;}
        }
    }
    std::cout<<"offset pairs "<<size<<", B templates "<<count.templates<<", A records "<<count.a
             <<", B probes "<<count.b<<", hash matches "<<count.overlaps<<", zero solutions\n";
}
