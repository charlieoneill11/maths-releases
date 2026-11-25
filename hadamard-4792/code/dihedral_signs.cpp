// Lift compatible binary supports by solving the coefficient equations
// modulo four, then check the Laurent polynomial identities over the integers.
#include "dihedral_support.hpp"
#include <algorithm>
#include <array>
#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <vector>

namespace {
using namespace binary_support;
using Word=std::uint64_t;
using Types=std::array<int,23>;
int n;
std::FILE* candidates=nullptr;
struct Term {
    Word vars=0;
    int constant=0;
    void add(int first,int second,int sign) {
        vars^=(Word(1)<<first)^(Word(1)<<second);
        constant+=sign;
    }
};
struct Linear {
    std::array<Word,46> row{};
    Word rhs=Word(1)<<(2*n);
    bool add(Word vars,int constant) {
        if(constant%2) return false;
        auto x=vars|((constant%4)?rhs:0);
        while(x&(rhs-1)) {
            int lead=__builtin_ctzll(x);
            if(!row[lead]) {row[lead]=x;return true;}
            x^=row[lead];
        }
        return !x;
    }
    bool add(const Term& t) {return add(t.vars,t.constant);}
    Word back(Word assignment) const {
        for(int i=2*n-1;i>=0;--i) if(row[i]) {
            if(__builtin_parityll(row[i]&assignment) != bool(row[i]&rhs)) assignment|=Word(1)<<i;
        }
        return assignment;
    }
};
Types types(Row r) {
    Types out{};
    for(int j=0;j<n;++j) out[j]=(r.i&bit(j))?1:(r.v&bit(j))?2:0;
    return out;
}
// Product sign for e_left e_right^T in the basis 1,i,s,is.
int norm_sign(int a,int b) {
    return a==0 && b==1 ? -1 : 1;
}
struct Atom {unsigned char a,b; signed char sign;};
struct Equations {
    std::vector<std::vector<Atom>> exact;
    Linear lin;
    bool insert(const std::vector<Atom>& terms) {
        if(terms.empty()) return true;
        Term t;
        for(auto x:terms) t.add(x.a,x.b,x.sign);
        if(!lin.add(t)) return false;
        exact.push_back(terms);
        return true;
    }
    bool verify(Word assignment) const {
        for(const auto& eq:exact) {
            int sum=0;
            for(auto term:eq) {
                int sign=((assignment>>term.a)^(assignment>>term.b))&1;
                sum+=sign?-term.sign:term.sign;
            }
            if(sum) return false;
        }
        return true;
    }
};
using Atoms=std::vector<Atom>;
Atom atom(int a,int b,int s) {
    return {static_cast<unsigned char>(a),static_cast<unsigned char>(b),static_cast<signed char>(s)};
}
bool setup(const Types& a,const Types& b,Equations& eq) {
    // Negate each whole sequence independently to fix both first signs.
    eq.lin.add(1,0);eq.lin.add(Word(1)<<n,0);
    if(n==23) for(int k=0;k<2;++k) for(int h=0;h<2;++h) {
        const auto& t=k?b:a;
        Word set=0;
        for(int j=h;j<n;j+=2) if(t[j]==2) set|=Word(1)<<(k*n+j);
        if(!eq.lin.add(set,__builtin_popcountll(set))) return false;
    }
    for(int k=n-1;k>0;--k) {
        std::array<Atoms,5> rows;
        for(int block=0;block<2;++block) {
            const auto& t=block?b:a;
            int pos=block*n;
            for(int j=k;j<n;++j) {
                int high=t[j],low=t[j-k],grade=high^low;
                // The is coordinate equals the divided self-commutator
                // I V* + V I* and must vanish for each row individually.
                auto target=grade==3?3+block:grade;
                rows[target].push_back(atom(pos+j,pos+j-k,norm_sign(high,low)));
            }
        }
        for(const auto& row:rows) if(!eq.insert(row)) return false;
    }
    // Divide the nonzero commutator coordinate by 2 before reducing mod 4.
    for(bool adjoint:{false,true}) for(int k=0;k<=2*(n-1);++k) {
        Atoms row;
        for(int j=std::max(0,k-n+1);j<=std::min(n-1,k);++j) {
            int h=adjoint?n-1-(k-j):k-j;
            if((a[j]^b[h])!=3) continue;
            int sign=(a[j]==1 || adjoint)?1:-1;
            row.push_back(atom(j,n+h,sign));
        }
        if(!eq.insert(row)) return false;
    }
    return true;
}
void emit(const Types& t,Word mask) {
    for(int j=0;j<n;++j) std::cout<<((mask>>j&1)?-1:1)*(1+t[j])<<' ';
    std::cout<<'\n';
}
struct Stats {Count pairs=0,consistent=0,lifts=0;std::array<Count,47> nullity{};};
bool solve(Row ar,Row br,Stats& stats) {
    ++stats.pairs;
    auto a=types(ar),b=types(br);
    Equations eq;
    if(!setup(a,b,eq)) return false;
    ++stats.consistent;
    auto& lin=eq.lin;
    std::vector<Word> basis;
    Word particular=lin.back(0);
    for(int j=0;j<2*n;++j) if(!lin.row[j]) basis.push_back(lin.back(Word(1)<<j)^particular);
    ++stats.nullity[basis.size()];
    Word signs=particular;
    for(Word m=0;m<(Word(1)<<basis.size());++m) {
        if(m) signs^=basis[__builtin_ctzll(m)];
        ++stats.lifts;
        if(candidates)
            std::fprintf(candidates,"%u %u %u %u %llu\n",ar.i,ar.v,br.i,br.v,
                         static_cast<unsigned long long>(signs));
        if(eq.verify(signs)) {
            emit(a,signs);emit(b,signs>>n);
            std::cout<<"DCS hit\n";return true;
        }
    }
    return false;
}
}
int main(int argc,char** argv) {
    if(argc!=3 && argc!=4) {std::cerr<<"usage: dihedral_signs odd_length primitive_width\n";return 2;}
    n=std::atoi(argv[1]);
    int width=std::atoi(argv[2]);
    if(n<3||n>23||n%2!=1||width<0||width>=n||width%2) return 2;
    if(argc==4) {candidates=std::fopen(argv[3],"w");if(!candidates) return 1;}
    Stats stats;
    Counts counts;
    bool hit=enumerate(n,width,[&](const auto& rows){
        for(unsigned i=0;i<rows.size();++i) for(unsigned j=0;j<=i;++j)
            if(solve(rows[i],rows[j],stats)) return true;
        return false;
    },counts);
    if(candidates) std::fclose(candidates);
    std::cout<<"n "<<n<<", width "<<width<<", support pairs "<<stats.pairs<<", mod-4 consistent "<<stats.consistent
             <<", sign lifts tried "<<stats.lifts<<", hits "<<hit<<", nullities";
    for(unsigned i=0;i<stats.nullity.size();++i) if(stats.nullity[i]) std::cout<<' '<<i<<'='<<stats.nullity[i];
    std::cout<<'\n';
}
