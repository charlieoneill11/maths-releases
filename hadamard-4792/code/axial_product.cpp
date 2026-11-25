// Exact Z_p x F3^2 quotient for a transitive or quadratic-residue prime action.
// The nontrivial spectrum has squared magnitude (real^2+p*imag^2)/4.
#include <array>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace {
using Four=std::array<int,4>;
using Key=std::array<int,7>;
int field,prime;
const int qr[4][4]={{1,4,4,0},{1,1,-2,0},{1,-2,1,0},{}};
const int klein[4][4]={{1,2,2,4},{1,-1,2,-2},{1,2,-1,-2},{1,-1,-1,1}};
const int (*T)[4];
using Plane=std::array<int,2>;
std::map<int,std::set<Plane>> pool;
std::set<Key> spectra;
std::uint64_t rows=0;
void choose(int at,const Four& d,std::array<Plane,4>& e,const Four& dc) {
    if(at<field) {
        for(auto v:pool.at(d[at])) {e[at]=v;choose(at+1,d,e,dc);}
        return;
    }
    Key k{};
    for(int i=1;i<field;++i) k[i-1]=dc[i]*dc[i];
    for(int i=0;i<field;++i) {
        int x=0,y=0;
        for(int j=0;j<field;++j) {x+=T[i][j]*e[j][0];y+=T[i][j]*e[j][1];}
        int power=(x*x+prime*y*y)/4;
        if(power>4792) return;
        k[field-1+i]=power;
    }
    spectra.insert(k);
    ++rows;
}
void totals(int at,int sum,Four& d) {
    if(at) {
        for(const auto& kv:pool) {d[at]=kv.first;totals(at-1,sum+T[0][at]*kv.first,d);}
        return;
    }
    d[0]=1-sum;
    if(!pool.count(d[0])) return;
    Four dc{};std::array<Plane,4> e{};
    for(int i=0;i<field;++i) {
        for(int j=0;j<field;++j) dc[i]+=T[i][j]*d[j];
        if(dc[i]*dc[i]>4792) return;
    }
    choose(0,d,e,dc);
}
}
int main(int argc,char**argv) {
    if(argc!=5) {std::cerr<<"usage: axial_product shape_file qr|klein 7|19 spectra_file\n";return 2;}
    std::ifstream input(argv[1]);
    int n,lags,p=std::atoi(argv[3]);
    input>>n>>lags;
    if(!input||n<1||n>17||(p!=7 && p!=19)) return 2;
    std::string type(argv[2]);
    if(type!="qr" && type!="klein") return 2;
    field=type=="qr"?3:4;T=field==3?qr:klein;
    std::vector<std::vector<int>> counts(n,std::vector<int>(p));
    for(int i=0;i<7;++i) for(int j=0;j<19;++j) {int x;input>>x;counts[x][p==7?i:j]++;}
    prime=p;
    std::vector<bool> square(p,false);
    for(int i=1;i<p;++i) square[i*i%p]=true;
    int non=1;while(square[non]) ++non;
    for(const auto& col:counts) for(int i=1;i<p;++i) if(col[i]!=col[square[i]?1:non]) {
        std::cerr<<"prime projection has more than two nonzero classes\n";return 2;
    }
    for(int mask=0;mask<(1<<n);++mask) {
        int a=0,b=0,c=0;
        for(int i=0;i<n;++i) {
            int v=mask>>i&1?-1:1;
            a+=v*counts[i][0];b+=v*counts[i][1];c+=v*counts[i][non];
        }
        pool[a+(p-1)/2*(b+c)].insert({2*a-b-c,b-c});
    }
    Four d{};totals(field-1,0,d);
    std::ofstream output(argv[4]);
    for(auto& row:spectra) for(int i=0;i<2*field-1;++i) output<<row[i]<<(i+1==2*field-1?'\n':' ');
    std::cout<<"prime "<<p<<", bounded axial rows "<<rows<<", distinct spectra "<<spectra.size()<<'\n';
}
