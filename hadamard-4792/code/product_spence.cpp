// Separate quadratic-residue multipliers on Z7 and Z19, with one of two
// order-four multiplier groups on F3^2. Evaluate every character over
// Q(sqrt(-7),sqrt(-19)); all power bounds below are integer inequalities.
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <vector>

namespace {
using Count=std::uint64_t;
using Feature=std::array<int,9>;
constexpr int order=4792;
constexpr int wt7[3]={1,3,3},wt19[3]={1,9,9},re[3]={2,-1,-1},im[3]={0,1,-1};
struct Sheet {Feature f{};int bits=0;};
struct State {std::array<int,4> sums{},bits{};};
const int qr[4][4]={{1,4,4,0},{1,1,-2,0},{1,-2,1,0},{}};
const int klein[4][4]={{1,2,2,4},{1,-1,2,-2},{1,2,-1,-2},{1,-1,-1,1}};
int field;
std::map<int,std::vector<Sheet>> sheets;
const int (*transform)[4];
Count sum_ok=0,power_ok=0,orientations=0;
std::map<std::array<int,3>,Count> classes;
std::FILE* stream=nullptr;

void setup() {
    for(int mask=0;mask<512;++mask) {
        Sheet s;s.bits=mask;
        for(int i=0;i<3;++i) for(int j=0;j<3;++j) {
            int x=(mask>>(3*i+j)&1)?-1:1;
            int terms[9]={wt7[i]*wt19[j],re[i]*wt19[j],im[i]*wt19[j],
                wt7[i]*re[j],wt7[i]*im[j],re[i]*re[j],im[i]*re[j],re[i]*im[j],im[i]*im[j]};
            for(int k=0;k<9;++k) s.f[k]+=x*terms[k];
        }
        sheets[s.f[0]].push_back(s);
    }
}
int reverse_mask(int m) {
    int out=0;
    constexpr int reverse[3]={0,2,1};
    for(int i=0;i<3;++i) for(int j=0;j<3;++j)
        out|=((m>>(3*i+j))&1)<<(3*reverse[i]+reverse[j]);
    return out;
}
void evaluate(const std::array<const Sheet*,4>& ss,const std::array<int,3>& dc) {
    ++sum_ok;
    // Individual full-group inversion preserves all character powers.
    for(int j=0;j<field;++j) {
        int a=ss[j]->bits,b=reverse_mask(a);
        if(a!=b) {if(a>b) return;break;}
    }
    ++orientations;
    std::array<int,20> powers{};
    for(int l=0;l<field;++l) {
        Feature f{};
        for(int j=0;j<field;++j) for(int k=0;k<9;++k) f[k]+=transform[l][j]*ss[j]->f[k];
        auto p=(f[1]*f[1]+7*f[2]*f[2])/4,q=(f[3]*f[3]+19*f[4]*f[4])/4;
        if(p>order || q>order) return;
        int x=f[5]*f[5]+7*f[6]*f[6]+19*f[7]*f[7]+133*f[8]*f[8];
        int y=2*(f[6]*f[7]-f[5]*f[8]);
        std::int64_t room=16*order-x;
        if(room<0 || room*room<std::int64_t(133)*y*y) return;
        powers[5*l]=f[0]*f[0];powers[5*l+1]=p;powers[5*l+2]=q;
        powers[5*l+3]=x;powers[5*l+4]=y;
    }
    ++power_ok;++classes[dc];
    if(stream) {
        for(int l=0;l<field;++l) std::fprintf(stream,"%d ",ss[l]->bits);
        for(int k=0;k<5*field;++k) std::fprintf(stream,"%d%c",powers[k],k+1==5*field?'\n':' ');
    }
}
void lists(int at,const State& st,std::array<const Sheet*,4>& ss,const std::array<int,3>& dc) {
    if(at==field) {evaluate(ss,dc);return;}
    for(const auto& s:sheets.at(st.sums[at])) {ss[at]=&s;lists(at+1,st,ss,dc);}
}
void totals(int at,int sum,State& st) {
    if(at) {
        for(const auto& item:sheets) {
            st.sums[at]=item.first;
            totals(at-1,sum+transform[0][at]*item.first,st);
        }
        return;
    }
    st.sums[0]=1-sum;
    if(!sheets.count(st.sums[0])) return;
    std::array<int,3> dc{};
    for(int l=1;l<field;++l) {
        int v=0;
        for(int j=0;j<field;++j) v+=transform[l][j]*st.sums[j];
        if(v*v>order) return;
        dc[l-1]=v*v;
    }
    std::array<const Sheet*,4> ss{};
    lists(0,st,ss,dc);
}
}
int main(int argc,char**argv) {
    if(argc!=2 && argc!=3) {std::cerr<<"usage: product_spence qr|klein [row_file]\n";return 2;}
    std::string choice(argv[1]);
    if(choice!="qr" && choice!="klein") return 2;
    field=choice=="qr"?3:4;
    transform=field==3?qr:klein;
    if(argc==3) {stream=std::fopen(argv[2],"w");if(!stream) return 1;}
    setup();State st;totals(field-1,0,st);
    if(stream) std::fclose(stream);
    std::cout<<choice<<", within field DC bounds "<<sum_ok<<", after inversion "<<orientations
             <<", within all character bounds "<<power_ok<<", DC classes "<<classes.size()<<'\n';
}
