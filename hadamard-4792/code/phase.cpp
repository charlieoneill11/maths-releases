// Integer lift search on the 17 K-orbits. An exact match on both prime
// quotients precedes the join on the remaining correlations.
#include <algorithm>
#include <array>
#include <cstdint>
#include <map>
#include <stdexcept>
#include <vector>

namespace {
constexpr int N=17;
using Word=std::uint64_t;
using Vec=std::array<int,N>;
using Margins=std::array<int,6>;
using Grid=std::array<std::array<Word,N>,N>;
struct Choice { unsigned mask; Word quadratic; };
using Fibres=std::map<Margins,std::vector<Choice>>;
struct Projected { Word key; const std::vector<Choice>* choices; };
struct Sheet {
    Vec s{}, e{};
    std::map<int,std::vector<Projected>> by_tau;
    std::array<Word,256> low{};
    std::array<Word,512> high{};
    Word constant=0;
    Word hash(const Choice &c) const {
        return constant+c.quadratic+low[c.mask&255]+high[c.mask>>8];
    }
};
Word mix(Word &state) {
    Word x=(state+=UINT64_C(0x9e3779b97f4a7c15));
    x=(x^(x>>30))*UINT64_C(0xbf58476d1ce4e5b9);
    x=(x^(x>>27))*UINT64_C(0x94d049bb133111eb);
    return x^(x>>31);
}
int norm(int p,int z,int a,int b) {
    int re=2*z-a-b, im=a-b;
    return (re*re+p*im*im)/4;
}
Word pack(const std::array<int,4>& v) {
    Word key=0;
    for (int x:v) key=(key<<14)+x;
    return key;
}

// All entries of every list are traversed; equal keys keep their indices.
template<class Key,class Hit>
bool meet(const std::array<int,4>& sizes, Word target, Key key, Hit hit) {
    std::array<int,4> p{0,1,2,3};
    std::sort(p.begin(),p.end(),[&](int i,int j){return sizes[i]<sizes[j];});
    int a=p[0],b=p[3],c=p[1],d=p[2];
    if (std::int64_t(sizes[a])*sizes[b]>std::int64_t(sizes[c])*sizes[d]) {
        std::swap(a,c); std::swap(b,d);
    }
    struct Entry {Word key; int x,y;};
    std::vector<Entry> table;
    table.reserve(std::size_t(sizes[a])*sizes[b]);
    for(int x=0;x<sizes[a];++x) for(int y=0;y<sizes[b];++y)
        table.push_back({key(a,x)+key(b,y),x,y});
    std::sort(table.begin(),table.end(),[](const auto& x,const auto& y){return x.key<y.key;});
    for(int z=0;z<sizes[c];++z) for(int w=0;w<sizes[d];++w) {
        Word need=target-key(c,z)-key(d,w);
        auto pos=std::lower_bound(table.begin(),table.end(),need,
                                  [](const auto& x,Word y){return x.key<y;});
        for(;pos!=table.end() && pos->key==need;++pos) {
            std::array<int,4> index;
            index[a]=pos->x; index[b]=pos->y; index[c]=z; index[d]=w;
            if(hit(index)) return true;
        }
    }
    return false;
}

struct Engine {
    int label[7][19]{};
    Vec weight{};
    std::array<Margins,N> contribution{};
    Grid A{}, B{};
    Word target=0;
    std::map<unsigned,Fibres> cache;
    struct TauPlan {
        std::array<std::array<bool,47>,4> allowed{};
        std::vector<std::array<int,4>> rows;
    };
    std::map<std::array<int,4>,TauPlan> plans;

    const TauPlan& tau_plan(const std::array<int,4>& sigmas) {
        auto inserted=plans.try_emplace(sigmas);
        auto& plan=inserted.first->second;
        if(!inserted.second) return plan;
        int required=4792;
        for(int v:sigmas) required-=v*v;
        if(required<0 || required%9) return plan;
        required/=9;
        std::array<std::vector<int>,4> choices;
        for(int i=0;i<4;++i) for(int t=-23;t<=23;++t)
            if((sigmas[i]-t)%2==0 && std::abs(sigmas[i])+3*std::abs(t)<=69)
                choices[i].push_back(t);
        for(int a:choices[0]) for(int b:choices[1])
        for(int c:choices[2]) for(int d:choices[3]) {
            std::array<int,4> t{a,b,c,d};
            int first=0,dot=0,squares=0;
            for(int i=0;i<4;++i) {
                if(!first) first=t[i];
                dot+=sigmas[i]*t[i];squares+=t[i]*t[i];
            }
            if(first<0 || dot || squares!=required) continue;
            plan.rows.push_back(t);
            for(int i=0;i<4;++i) plan.allowed[i][t[i]+23]=true;
        }
        return plan;
    }

    explicit Engine(const std::int16_t* labels) {
        constexpr int reps[6]={0,1,3,0,1,2};
        for(int i=0;i<7;++i) for(int j=0;j<19;++j) {
            int o=labels[19*i+j];
            if(o<0 || o>=N) throw std::invalid_argument("orbit label");
            label[i][j]=o;
            ++weight[o];
            for(int k=0;k<6;++k) contribution[o][k]+=(k<3?i:j)==reps[k];
        }
        Word state=4792;
        for(int i=0;i<7;++i) for(int j=0;j<19;++j) {
            Word a=mix(state),b=mix(state);
            if(i==0 && j==0) target=4792*a;
            for(int x=0;x<7;++x) for(int y=0;y<19;++y) {
                int u=label[x][y],v=label[(x+i)%7][(y+j)%19];
                A[u][v]+=a; B[u][v]+=b;
            }
        }
    }

    const Fibres& pool(unsigned active) {
        auto ins=cache.try_emplace(active);
        Fibres& fibres=ins.first->second;
        if(!ins.second) return fibres;
        Vec t{}; std::vector<int> free;
        Margins margin{};
        for(int i=0;i<N;++i) if(active & (1u<<i)) {
            free.push_back(i); t[i]=-1;
            for(int k=0;k<6;++k) margin[k]-=contribution[i][k];
        }
        std::array<Word,N> gradient{};
        Word q=0;
        for(int i:free) for(int j:free) {
            q+=A[i][j];
            if(i!=j) gradient[i]-=A[i][j]+A[j][i];
        }
        unsigned mask=0;
        for(unsigned index=0;index<(1u<<free.size());++index) {
            if(index) {
                int i=free[__builtin_ctz(index)], delta=-2*t[i];
                mask^=1u<<i;
                q+=Word(delta)*gradient[i];
                for(int j:free) if(i!=j) gradient[j]+=Word(delta)*(A[j][i]+A[i][j]);
                for(int k=0;k<6;++k) margin[k]+=delta*contribution[i][k];
                t[i]=-t[i];
            }
            fibres[margin].push_back({mask,9*q});
        }
        return fibres;
    }

    Sheet prepare(const std::int8_t* u,const std::array<bool,47>& allowed) {
        Sheet row;
        unsigned active=0;
        Margins sm{};
        for(int i=0;i<N;++i) {
            int x=u[i],a=std::abs(x);
            if(a!=1 && a!=7 && a!=9) throw std::invalid_argument("u value");
            row.e[i]=a==1?0:(x>0?1:-1);
            row.s[i]=x-9*row.e[i];
            if(a==1) active|=1u<<i;
            for(int k=0;k<6;++k) sm[k]+=row.s[i]*contribution[i][k];
        }
        std::array<Word,N> lin{};
        for(int i=0;i<N;++i) for(int j=0;j<N;++j) {
            row.constant+=Word(row.s[i])*A[i][j]*Word(row.s[j]);
            lin[i]+=(B[i][j]+B[j][i])*Word(row.s[j]);
        }
        for(int i=0;i<N;++i) if(active & (1u<<i)) row.constant-=lin[i];
        for(unsigned i=1;i<row.low.size();++i)
            row.low[i]=row.low[i&(i-1)]+2*lin[__builtin_ctz(i)];
        for(unsigned i=1;i<row.high.size();++i)
            row.high[i]=row.high[i&(i-1)]+2*lin[8+__builtin_ctz(i)];
        for(const auto& item:pool(active)) {
            const auto &t=item.first;
            int tau=t[0]+3*(t[1]+t[2]);
            if(std::abs(tau)>23 || !allowed[tau+23]) continue;
            std::array<int,4> powers{};
            int k=0;
            for(int offset:{0,3}) for(int f:{-3,3}) {
                auto h=[&](int r){return sm[offset+r]+f*t[offset+r];};
                powers[k++]=norm(offset?19:7,h(0),h(1),h(2));
            }
            if(*std::max_element(powers.begin(),powers.end())<=4792)
                row.by_tau[tau].push_back({pack(powers),&item.second});
        }
        return row;
    }

    bool exact(const std::array<Sheet,4>& rows,const std::array<unsigned,4>& masks) const {
        for(int i=0;i<7;++i) for(int j=0;j<19;++j) {
            int actual[3]={};
            for(int k=0;k<4;++k) for(int a=0;a<7;++a) for(int b=0;b<19;++b) {
                int o=label[a][b], h=label[(a+i)%7][(b+j)%19];
                const auto &r=rows[k];
                auto t=[&](int z){return r.e[z]?0:((masks[k]>>z)&1u?1:-1);};
                actual[0]+=(r.s[o]+9*r.e[o])*(r.s[h]+9*r.e[h]);
                actual[1]+=(r.s[o]+3*t(o))*(r.s[h]+3*t(h));
                actual[2]+=(r.s[o]-3*t(o))*(r.s[h]-3*t(h));
            }
            int target_paf=(i==0 && j==0)?4792:0;
            if(actual[0]!=target_paf-36 || actual[1]!=target_paf || actual[2]!=target_paf)
                return false;
        }
        return true;
    }

    bool search(const std::int8_t* u,std::uint32_t* answer,std::uint64_t* counts) {
        std::array<int,4> sigmas{};
        for(int i=0;i<4;++i) for(int j=0;j<N;++j) {
            int x=u[N*i+j],e=std::abs(x)==1?0:(x>0?1:-1);
            sigmas[i]+=weight[j]*(x-9*e);
        }
        const auto& plan=tau_plan(sigmas);
        if(plan.rows.empty()) return false;
        std::array<Sheet,4> rows;
        for(int i=0;i<4;++i) rows[i]=prepare(u+N*i,plan.allowed[i]);
        std::array<int,4> sizes;
        using Group=std::vector<Projected>;
        for(const auto& ts:plan.rows) {
            const Group* g[4]={};
            bool present=true;
            for(int i=0;i<4;++i) {
                auto it=rows[i].by_tau.find(ts[i]);
                if(it==rows[i].by_tau.end()) {present=false;break;}
                g[i]=&it->second;
                sizes[i]=int(g[i]->size());
            }
            if(!present) continue;
            ++counts[0];
            const auto field_key=[&](int i,int n){return (*g[i])[n].key;};
            bool found=meet(sizes,pack({4792,4792,4792,4792}),field_key,[&](const auto& at){
                ++counts[1];
                const std::vector<Choice>* fibres[4];
                std::array<int,4> lengths;
                for(int i=0;i<4;++i) {fibres[i]=(*g[i])[at[i]].choices; lengths[i]=int(fibres[i]->size());}
                const auto full_hash=[&](int i,int n){return rows[i].hash((*fibres[i])[n]);};
                return meet(lengths,target,full_hash,[&](const auto& hit){
                    ++counts[2];
                    std::array<unsigned,4> masks;
                    for(int i=0;i<4;++i) masks[i]=(*fibres[i])[hit[i]].mask;
                    if(!exact(rows,masks)) return false;
                    std::copy(masks.begin(),masks.end(),answer);
                    return true;
                });
            });
            if(found) return true;
        }
        return false;
    }
};
}

extern "C" void* create_phase(const std::int16_t* labels) {
    try {return new Engine(labels);} catch (...) {return nullptr;}
}
extern "C" void delete_phase(void* ptr) {delete static_cast<Engine*>(ptr);}
extern "C" int phase_batch(void* ptr,const std::int8_t* u,int n,std::uint32_t* masks,std::uint64_t* counts) {
    try {
        for(int i=0;i<n;++i)
            if(static_cast<Engine*>(ptr)->search(u+4*N*i,masks,counts)) return i;
        return -1;
    } catch (...) {return -2;}
}

// The control passes an externally computed fingerprint of a stored projected
// solution. The full Spence test remains active even when using this fingerprint.
extern "C" int planted_phase(const std::int16_t* labels,const std::int8_t* u,
                             std::uint64_t fingerprint,std::uint64_t* counts) {
    try {
        Engine engine(labels);
        engine.target=fingerprint;
        std::uint32_t masks[4]{};
        return engine.search(u,masks,counts)?1:0;
    } catch (...) {return -1;}
}
