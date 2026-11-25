// Generate all sign blocks for an input orbit partition of Z7 x Z19 and
// one of two field actions on F3^2. Native int32 records are temporary input
// for orbit_join.py. Fourier rejection uses integral Rayleigh quotients.
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <vector>

namespace {
constexpr int cap=16,order=4792;
using I=std::int64_t;
using Count=std::uint64_t;
using Vec=std::array<int,cap>;
using Plane=std::array<Vec,cap>;
using Four=std::array<int,4>;
struct Sheet {int mask=0,mirror=0;Vec re{},im{};};
int n,nlags,field;
std::array<int,133> labels;
Vec weights{},reps{},norm{};
Plane realcoef{},imagcoef{};
std::array<Plane,cap> acf{};
std::map<int,std::vector<Sheet>> groups;
const int qr[4][4]={{1,4,4,0},{1,1,-2,0},{1,-2,1,0},{}};
const int klein[4][4]={{1,2,2,4},{1,-1,2,-2},{1,2,-1,-2},{1,-1,-1,1}};
const int (*T)[4];
Count dc_count=0,oriented=0,passing=0;
std::FILE* output=nullptr;

bool read_shape(const char* file) {
    std::ifstream input(file);
    input>>n>>nlags;
    if(!input || n<1 || n>cap || nlags<1 || nlags>cap) return false;
    for(auto& x:labels) input>>x;
    for(int o=0;o<n;++o) input>>weights[o];
    for(int k=0;k<nlags;++k) input>>reps[k];
    for(int k=1;k<nlags;++k) {
        input>>norm[k];
        for(int i=0;i<n;++i) input>>realcoef[k][i];
        for(int i=0;i<n;++i) input>>imagcoef[k][i];
    }
    for(int k=0;k<nlags;++k) for(int i=0;i<n;++i) for(int j=0;j<n;++j) input>>acf[k][i][j];
    return bool(input);
}
void setup() {
    std::array<int,cap> rev{};
    for(int a=0;a<7;++a) for(int b=0;b<19;++b)
        rev[labels[19*a+b]]=labels[19*((7-a)%7)+(19-b)%19];
    for(int mask=0;mask<(1<<n);++mask) {
        Sheet s;s.mask=mask;int sum=0;
        for(int o=0;o<n;++o) {
            int v=(mask>>o&1)?-1:1;
            sum+=weights[o]*v;
            if(v<0) s.mirror|=1<<rev[o];
            for(int k=1;k<nlags;++k) {s.re[k]+=v*realcoef[k][o];s.im[k]+=v*imagcoef[k][o];}
        }
        groups[sum].push_back(s);
    }
}
void evaluate(const std::array<const Sheet*,4>& ss,const Four& dc) {
    ++dc_count;
    for(int j=0;j<field;++j) if(ss[j]->mask!=ss[j]->mirror) {
        if(ss[j]->mask>ss[j]->mirror) return;
        break;
    }
    ++oriented;
    for(int l=0;l<field;++l) for(int k=1;k<nlags;++k) {
        int a=0,b=0;
        for(int j=0;j<field;++j) {a+=T[l][j]*ss[j]->re[k];b+=T[l][j]*ss[j]->im[k];}
        if(I(a)*a+I(b)*b>I(order)*norm[k]*norm[k]) return;
    }
    ++passing;
    if(!output) return;
    std::array<std::int32_t,4*(cap+2)> record{};
    for(int j=0;j<field;++j) {record[j]=ss[j]->mask;record[field+j]=dc[j]*dc[j];}
    for(int l=0;l<field;++l) {
        Vec v{};
        for(int o=0;o<n;++o) for(int j=0;j<field;++j) v[o]+=T[l][j]*((ss[j]->mask>>o&1)?-1:1);
        for(int k=0;k<nlags;++k) {
            int a=0;
            for(int i=0;i<n;++i) {
                int b=0;
                for(int j=0;j<n;++j) b+=acf[k][i][j]*v[j];
                a+=b*v[i];
            }
            record[2*field+l*nlags+k]=a;
        }
    }
    if(std::fwrite(record.data(),sizeof(record[0]),field*(2+nlags),output)!=std::size_t(field*(2+nlags))) {
        std::perror("write rows");std::exit(1);
    }
}
void lists(int at,const Four& sums,std::array<const Sheet*,4>& ss,const Four& dc) {
    if(at==field) {evaluate(ss,dc);return;}
    for(const auto& s:groups.at(sums[at])) {ss[at]=&s;lists(at+1,sums,ss,dc);}
}
void totals(int at,int sum,Four& sums) {
    if(at) {
        for(const auto& item:groups) {
            sums[at]=item.first;totals(at-1,sum+T[0][at]*item.first,sums);
        }
        return;
    }
    sums[0]=1-sum;
    if(!groups.count(sums[0])) return;
    Four dc{};
    for(int l=0;l<field;++l) {
        for(int j=0;j<field;++j) dc[l]+=T[l][j]*sums[j];
        if(dc[l]*dc[l]>order) return;
    }
    std::array<const Sheet*,4> ss{};
    lists(0,sums,ss,dc);
}
}
int main(int argc,char**argv) {
    if(argc!=3 && argc!=4) {std::cerr<<"usage: orbit_spence shape_file qr|klein [rows.bin]\n";return 2;}
    std::string fieldname(argv[2]);
    if(fieldname!="qr" && fieldname!="klein") return 2;
    field=fieldname=="qr"?3:4;
    T=field==3?qr:klein;
    if(!read_shape(argv[1])) return 2;
    if(argc==4) {output=std::fopen(argv[3],"wb");if(!output) return 1;}
    setup();Four sums{};totals(field-1,0,sums);
    if(output && std::fclose(output)) return 1;
    std::cout<<fieldname<<", K orbits "<<n<<", K lags "<<nlags<<", within DC bounds "<<dc_count
             <<", after inversion "<<oriented<<", within integral power bounds "<<passing<<'\n';
}
