// Enumerate ternary supports directly by choosing the two outside letters
// at each depth. This code does not use the primitive-width decomposition.
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <vector>

namespace {
using Mask=std::uint32_t;
using Word=std::uint64_t;
int n;
Mask all;
std::array<Mask,23> edges;
int parity(Mask x) {return __builtin_parity(x);}
Mask reverse(Mask x) {
    Mask result=0;
    for(;x;x&=x-1) result|=Mask(1)<<(n-1-__builtin_ctz(x));
    return result;
}
int degree(Mask x) {return 31-__builtin_clz(x);}
Mask divide(Mask a,Mask b,Mask& r) {
    Mask q=0;r=a;
    while(r && degree(r)>=degree(b)) {
        int k=degree(r)-degree(b);
        r^=b<<k;q|=Mask(1)<<k;
    }
    return q;
}
Mask gcd(Mask a,Mask b) {
    while(b) {Mask r;divide(a,b,r);a=b;b=r;}
    return a;
}
struct Row {Mask i,v;};
using Key=std::array<Word,4>;
std::map<Key,std::vector<Row>> groups;
Word leaves=0,rows=0,pairs=0;
bool self(Mask i,Mask s,int lag) {return !parity(((i>>lag)&s)^((s>>lag)&i));}
void store(Mask i,Mask v) {
    ++leaves;
    if(!i||!v) return;
    if(n==23 && (parity(v&0x55555555u)||parity(v&0xaaaaaaaau))) return;
    for(int k=1;k<n/2;++k) if(!self(i,v,k)) return;
    if(std::array<Mask,2>{i,v}>std::array<Mask,2>{reverse(i),reverse(v)}) return;
    Mask g=gcd(i,v),tmp;
    Key key={divide(i,g,tmp),divide(v,g,tmp),0,0};
    Mask r=all^i^v;
    for(int k=1;k<n;++k) {
        // In characteristic two signs disappear. Product grades are XOR.
        int scalar=parity((r&(r>>k))^(i&(i>>k))^(v&(v>>k)));
        int imag=parity((r&(i>>k))^(i&(r>>k)));
        int refl=parity((r&(v>>k))^(v&(r>>k)));
        key[2]=(key[2]<<2)|(scalar<<1)|imag;
        key[3]=(key[3]<<1)|refl;
    }
    groups[key].push_back({i,v});
    ++rows;
}
void extend(int j,Mask i,Mask v) {
    int h=n-1-j;
    if(j>h) {store(i,v);return;}
    auto a=edges[j],b=edges[h];
    for(int left=0;left<3;++left) for(int right=0;right<3;++right) {
        if(j==h && left!=right) continue;
        auto ni=i|(left==1?a:0)|(right==1?b:0);
        auto nv=v|(left==2?a:0)|(right==2?b:0);
        if(self(ni,nv,h)) extend(j+1,ni,nv);
    }
}
}
int main(int argc,char** argv) {
    if(argc!=2 && argc!=3) return 2;
    n=std::atoi(argv[1]);
    if(n<3||n>23||n%2!=1) return 2;
    all=(Mask(1)<<n)-1;
    for(int i=0;i<n;++i) edges[i]=Mask(1)<<i;
    extend(0,0,0);
    std::FILE* dump=argc==3?std::fopen(argv[2],"w"):nullptr;
    if(argc==3 && !dump) return 1;
    for(const auto& group:groups) {
        const auto& v=group.second;
        pairs+=Word(v.size())*(v.size()+1)/2;
        if(!dump) continue;
        for(unsigned i=0;i<v.size();++i) for(unsigned j=0;j<=i;++j) {
            std::array<Mask,2> a{v[i].i,v[i].v},b{v[j].i,v[j].v};
            if(b<a) std::swap(a,b);
            std::fprintf(dump,"%06x %06x %06x %06x\n",a[0],a[1],b[0],b[1]);
        }
    }
    if(dump) std::fclose(dump);
    std::cout<<"n "<<n<<", terminal supports "<<leaves<<", retained rows "<<rows
             <<", unordered support pairs "<<pairs<<'\n';
}
