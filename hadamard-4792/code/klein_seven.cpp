// The remaining 12-K-orbit Klein case has K multipliers +/-1 on Z7 and
// the nine squares on Z19. Exhaust its Z7 x F3^2 quotient.
#include <array>
#include <cstdint>
#include <cstdio>
#include <iostream>
#include <map>
#include <vector>

namespace {
using Row=std::array<int,4>;
using Sites=std::array<Row,4>;
using Count=std::uint64_t;
const int signs[6]={-19,-17,-1,1,17,19};
const int t[4][4]={{1,2,2,4},{1,-1,2,-2},{1,2,-1,-2},{1,-1,-1,1}};
int maxenergy(int l) {return l?4792:4108;}
Count tested=0,energy_pass=0,passed=0;
std::map<Row,Count> classes;
std::FILE* out=nullptr;

std::vector<Row> local(int weight) {
    std::vector<Row> result;
    for(int a:signs) for(int b:signs) for(int c:signs) for(int d:signs) {
        Row r{},cell{a,b,c,d};
        bool ok=true;
        for(int l=0;l<4;++l) {
            for(int j=0;j<4;++j) r[l]+=t[l][j]*cell[j];
            if(weight*r[l]*r[l]>maxenergy(l)) ok=false;
        }
        if(ok) result.push_back(r);
    }
    return result;
}
void check(const Sites& cols) {
    ++tested;
    Row dc{},energy{};
    for(int l=0;l<4;++l) {
        for(int i=0;i<4;++i) {
            int w=i?2:1;
            dc[l]+=w*cols[i][l];energy[l]+=w*cols[i][l]*cols[i][l];
        }
        if(dc[l]*dc[l]>4792 || energy[l]>maxenergy(l)) return;
    }
    ++energy_pass;
    // v=(4,2,-1,-4,-4,-1,2). The other two tests permute indices by units.
    // If a full lift exists, ||C v||^2 <= 4792 ||v||^2 for every field channel.
    constexpr int v[7]={4,2,-1,-4,-4,-1,2};
    int norm=0;for(int a:v) norm+=a*a;
    std::array<std::int32_t,36> record{};
    for(int i=0;i<4;++i) for(int l=0;l<4;++l) record[4*i+l]=cols[i][l];
    for(int l=0;l<4;++l) {
        std::array<int,7> f{cols[0][l],cols[1][l],cols[2][l],cols[3][l],cols[3][l],cols[2][l],cols[1][l]};
        record[16+l]=dc[l]*dc[l];
        for(int k=0;k<4;++k) {
            int y=0;for(int j=0;j<7;++j) y+=f[j]*f[(j+k)%7];
            record[20+4*l+k]=y;
        }
        for(int q=1;q<=3;++q) {
            int sum=0;
            for(int h=0;h<7;++h) {
                int z=0;for(int j=0;j<7;++j) z+=f[j]*v[q*(h+j)%7];
                sum+=z*z;
            }
            if(sum>4792*norm) return;
        }
    }
    ++passed;
    Row key;for(int i=0;i<4;++i) key[i]=dc[i]*dc[i];
    ++classes[key];
    if(out && std::fwrite(record.data(),sizeof(record[0]),record.size(),out)!=record.size()) {
        std::perror("write quotient rows");std::exit(1);
    }
}
}
int main(int argc,char**argv) {
    if(argc!=1 && argc!=2) return 2;
    if(argc==2) {out=std::fopen(argv[1],"wb");if(!out) return 1;}
    auto origin=local(1),nonzero=local(2);
    std::map<int,std::vector<std::array<int,2>>> pairs;
    for(int i=0;i<int(nonzero.size());++i) for(int j=0;j<int(nonzero.size());++j)
        pairs[2*(nonzero[i][0]+nonzero[j][0])].push_back({i,j});
    for(auto a:origin) for(auto b:nonzero) {
        auto it=pairs.find(1-a[0]-2*b[0]);
        if(it==pairs.end()) continue;
        for(auto ij:it->second) check({a,b,nonzero[ij[0]],nonzero[ij[1]]});
    }
    if(out && std::fclose(out)) return 1;
    std::cout<<origin.size()<<" origin values, "<<nonzero.size()<<" nonzero-site values, "
             <<tested<<" sum-one rows, "<<energy_pass<<" rows within energy and DC bounds, "
             <<passed<<" after integral character bounds, "<<classes.size()<<" DC classes\n";
}
