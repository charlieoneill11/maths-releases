// One sequence is entirely real, and the other has symmetric R,I and skew V.
// First eliminate B supports by the mod-4 periodic autocorrelations of A.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

namespace {
using Mask=std::uint32_t;
using Word=std::uint64_t;
int n;
Mask all;
std::array<Word,23> weights;
int pop(Mask x) {return __builtin_popcount(x);}
struct Row {
    std::array<Mask,3> support{},negative{};
    int corr(int d) const {
        int v=0;
        for(int t=0;t<3;++t) {
            Mask both=support[t]&(support[t]>>d);
            v+=pop(both)-2*pop(both&(negative[t]^(negative[t]>>d)));
        }
        return v;
    }
    Word hash() const {
        Word v=0;
        for(int k=1;k<n;++k) v+=Word(corr(k))*weights[k];
        return v;
    }
};
int real_corr(Mask neg,int k) {
    return n-k-2*pop((neg^(neg>>k))&(all>>k));
}
using Entry=std::pair<Word,Mask>;
struct Counts {Word tested=0,supports=0,signs=0,matches=0;};
bool search(const std::vector<Entry>& table,int pattern,int center,Counts& count) {
    ++count.tested;
    Row r;
    r.support[center]|=Mask(1)<<(n/2);
    for(int j=0;j<n/2;++j) {
        int t=pattern%3;pattern/=3;
        Mask left=Mask(1)<<j,right=Mask(1)<<(n-1-j);
        r.support[t]|=left|right;
        if(t==2) r.negative[t]|=right;
    }
    for(int k=1;k<=n/2;++k) if((n+r.corr(k)+r.corr(n-k))%4) return false;
    ++count.supports;
    std::vector<std::pair<int,Mask>> free;
    for(int t=0;t<3;++t) {
        bool first=true;
        for(int j=0;j<=n/2;++j) if(r.support[t]&(Mask(1)<<j)) {
            if(!first) free.emplace_back(t,(Mask(1)<<j)|(Mask(1)<<(n-1-j)));
            first=false;
        }
    }
    for(unsigned j=0;j<(Mask(1)<<free.size());++j) {
        if(j) {auto [t,b]=free[__builtin_ctz(j)];r.negative[t]^=b;}
        ++count.signs;
        Word wanted=0-r.hash();
        auto it=std::lower_bound(table.begin(),table.end(),Entry{wanted,0});
        for(;it!=table.end() && it->first==wanted;++it) {
            ++count.matches;
            bool good=true;
            for(int k=1;k<n;++k) if(real_corr(it->second,k)+r.corr(k)) {good=false;break;}
            if(!good) continue;
            for(int k=0;k<n;++k) std::cout<<((it->second>>k&1)?-1:1)<<' ';
            std::cout<<'\n';
            for(int k=0;k<n;++k) for(int t=0;t<3;++t) if((r.support[t]>>k)&1)
                std::cout<<((r.negative[t]>>k&1)?-1:1)*(t+1)<<' ';
            std::cout<<"\nDCS hit\n";return true;
        }
    }
    return false;
}
}
int main(int argc,char** argv) {
    if(argc!=2) return 2;
    n=std::atoi(argv[1]);
    if(n<3||n>23||n%2!=1) return 2;
    all=(Mask(1)<<n)-1;
    Word seed=23;
    for(auto& w:weights) {
        seed+=UINT64_C(0x9e3779b97f4a7c15);
        auto x=(seed^(seed>>30))*UINT64_C(0xbf58476d1ce4e5b9);
        x=(x^(x>>27))*UINT64_C(0x94d049bb133111eb);w=x^(x>>31);
    }
    std::vector<Entry> table;
    for(Mask a=0;a<=all;a+=2) {
        int s=n-2*pop(a);
        if(s*s>2*n) continue;
        Word h=0;
        for(int k=1;k<n;++k) h+=weights[k]*Word(real_corr(a,k));
        table.emplace_back(h,a);
    }
    std::sort(table.begin(),table.end());
    int limit=1;
    for(int i=0;i<n/2;++i) limit*=3;
    Counts count;
    for(int p=0;p<limit;++p) for(int center=0;center<2;++center)
        if(search(table,p,center,count)) return 0;
    std::cout<<"n "<<n<<", real rows "<<table.size()<<", raw type patterns "<<count.tested
             <<", periodic-mod-4 survivors "<<count.supports<<", signed rows "<<count.signs
             <<", fingerprint matches "<<count.matches<<", zero solutions\n";
}
