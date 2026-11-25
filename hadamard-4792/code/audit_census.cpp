// Independent row-sum census. Enumerate multisets of the actual eight field
// sign triples on the fourteen weight-nine orbits, then assign the three
// light orbits explicitly. Output one sorted normalized specification per line.
#include <algorithm>
#include <array>
#include <cmath>
#include <iostream>
#include <map>
#include <set>
#include <vector>

namespace {
using State=std::array<int,5>; // n, m, sigma, epsilon, tau
using Spec=std::array<int,4>;
using Band=std::array<Spec,4>;
using F=std::array<int,3>; // defect cost and the two nontrivial field powers

State add(State x,const State& y,int d=1) {
    for(int i=0;i<5;++i) x[i]+=d*y[i];
    return x;
}

struct Census {
    std::vector<State> letters;
    std::set<State> light,states;
    Census() {
        for(int a:{-1,1}) for(int b:{-1,1}) for(int c:{-1,1}) {
            int e=(b+c)/2;
            letters.push_back({int(b==c),int(b==c && a!=b),a-e,e,(b-c)/2});
        }
        for(auto a:letters) for(auto b:letters) for(auto c:letters)
            light.insert(add(add(a,b,3),c,3));
    }
    void heavy(int i,int left,State x) {
        if(i<7) {
            for(int n=0;n<=left;++n) heavy(i+1,left-n,add(x,letters[i],9*n));
            return;
        }
        x=add(x,letters[7],9*left);
        for(auto l:light) {
            State z=add(x,l);
            if(std::abs(z[2]+9*z[3])!=1 || 10*z[0]-4*z[1]>528) continue;
            if(std::abs(z[2])+3*std::abs(z[4])>69) continue;
            if(z[2]<0 || (z[2]==0 && z[3]<0)) for(int k:{2,3,4}) z[k]=-z[k];
            states.insert(z);
        }
    }
};
}
int main() {
    Census c;
    c.heavy(0,14,{});
    std::map<F,std::set<Spec>> features;
    for(auto z:c.states) {
        int u=z[2]+3*z[4],v=z[2]-3*z[4];
        features[{10*z[0]-4*z[1],u*u,v*v}].insert({z[0],z[1],z[2],z[3]});
    }
    std::vector<F> fs;
    for(auto &entry:features) fs.push_back(entry.first);
    using Pair=std::array<int,2>;
    std::map<F,std::vector<Pair>> pairs;
    for(int i=0;i<int(fs.size());++i) for(int j=i;j<int(fs.size());++j) {
        F f={fs[i][0]+fs[j][0],fs[i][1]+fs[j][1],fs[i][2]+fs[j][2]};
        if(f[0]<=528 && f[1]<=4792 && f[2]<=4792) pairs[f].push_back({i,j});
    }
    std::set<Band> bands;
    for(const auto &e:pairs) {
        auto it=pairs.find({528-e.first[0],4792-e.first[1],4792-e.first[2]});
        if(it==pairs.end() || it->first<e.first) continue;
        for(auto ab:e.second) for(auto cd:it->second)
            for(auto a:features[fs[ab[0]]]) for(auto b:features[fs[ab[1]]])
            for(auto d:features[fs[cd[0]]]) for(auto f:features[fs[cd[1]]]) {
                Band band{a,b,d,f};
                std::sort(band.begin(),band.end());
                bands.insert(band);
            }
    }
    for(const auto &band:bands) {
        for(auto r:band) for(int x:r) std::cout<<x<<' ';
        std::cout<<'\n';
    }
}
