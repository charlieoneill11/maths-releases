#include "dihedral_support.hpp"
#include <cstdlib>
#include <cstdio>
#include <algorithm>
#include <iostream>
int main(int argc,char**argv) {
    if(argc!=3 && argc!=4) return 2;
    int n=std::atoi(argv[1]),L=std::atoi(argv[2]);
    if(n<3||n>23||n%2!=1||L<0||L>=n||L%2) return 2;
    binary_support::Counts count;
    std::FILE* dump=argc==4?std::fopen(argv[3],"w"):nullptr;
    if(argc==4 && !dump) return 1;
    binary_support::enumerate(n,L,[&](const auto& rows){
        if(!dump) return false;
        auto form=[&](const auto& r) {
            using namespace binary_support;
            return std::min(std::array<Mask,2>{r.i,r.v},std::array<Mask,2>{reverse(r.i,n),reverse(r.v,n)});
        };
        for(unsigned i=0;i<rows.size();++i) for(unsigned j=0;j<=i;++j) {
            auto a=form(rows[i]),b=form(rows[j]);
            if(b<a) std::swap(a,b);
            std::fprintf(dump,"%06x %06x %06x %06x\n",a[0],a[1],b[0],b[1]);
        }
        return false;
    },count);
    if(dump) std::fclose(dump);
    std::cout<<"n "<<n<<", width "<<L<<", primitive pairs "<<count.reduced
             <<", rows "<<count.rows<<", unordered support pairs "<<count.pairs<<'\n';
}
