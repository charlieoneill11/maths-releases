// Generate the field-trivial K blocks with specified margin types on 7 and 19.
// Grouping the two seven-letter lists by their exact contributions makes the
// enumeration independent of the size of the unrestricted block list.
#include <algorithm>
#include <array>
#include <cstdint>
#include <map>
#include <vector>
#include <new>

namespace {
using Triple=std::array<int,3>;
using Word=std::uint64_t;
using Table=std::map<int,std::map<Triple,std::vector<Word>>>;
constexpr int OFFSET=171*77*400+38*400;
constexpr int values[6]={-9,-7,-1,1,7,9};

int code(int u) {
    int e=u>1?1:u< -1?-1:0;
    int s=u-9*e;
    return ((u*77+s)*20+(e!=0))*20+(s*e==-2);
}

Table half(const std::int16_t *labels,int j) {
    Table tab;
    int positions=j?7:3;
    int count=1;
    for(int k=0;k<positions;++k) count*=6;
    for(int n=0;n<count;++n) {
        int word=n,sum=0; Word mask=0; Triple partial{};
        for(int k=0;k<positions;++k) {
            int rank=word%6; word/=6;
            int x=j?k:(k==2?3:k);
            int cls=x==0?0:(x==1||x==2||x==4)?1:2;
            int letter=code(values[rank]);
            sum+=(j || x==0?1:3)*letter;
            partial[cls]+=(j?(x==0?9:3):1)*letter;
            mask|=Word(rank)<<(3*(16-labels[19*x+j]));
        }
        tab[OFFSET+sum][partial].push_back(mask);
    }
    return tab;
}

bool canonical(Word m,const std::int16_t* perms,int count) {
    for(int i=0;i<count;++i) {
        for(int j=0;j<17;++j) {
            unsigned a=(m>>(3*(16-j)))&7;
            unsigned b=(m>>(3*(16-perms[17*i+j])))&7;
            if(b<a) return false;
            if(b>a) break;
        }
    }
    return true;
}

struct Tables {
    Table light,left,right;
    explicit Tables(const std::int16_t* labels):
        light(half(labels,0)),left(half(labels,1)),right(half(labels,2)) {}
};
}

extern "C" void* build_margin_tables(const std::int16_t* labels) {
    try {return new Tables(labels);} catch(...) {return nullptr;}
}
extern "C" void free_margin_tables(void* tables) {delete static_cast<Tables*>(tables);}
extern "C" void free_block_words(Word* data) {delete[] data;}

extern "C" std::int64_t margin_blocks(void* tables,const int* f7,int n7,const int* f19,int n19,
                                      const std::int16_t* perms,int count,Word** result) {
    try {
        const auto &T=*static_cast<Tables*>(tables);
        std::vector<Word> out;
        for(int p=0;p<n19;++p) {
            auto zero=T.light.find(f19[3*p]);
            auto a=T.left.find(f19[3*p+1]);
            auto b=T.right.find(f19[3*p+2]);
            if(zero==T.light.end() || a==T.left.end() || b==T.right.end()) continue;
            auto A=&a->second,B=&b->second;
            if(A->size()>B->size()) std::swap(A,B);
            for(const auto& fixed:zero->second) for(int q=0;q<n7;++q) {
                Triple target;
                for(int i=0;i<3;++i) target[i]=f7[3*q+i]-OFFSET-fixed.first[i];
                for(const auto& left:*A) {
                    Triple need;
                    for(int i=0;i<3;++i) need[i]=target[i]-left.first[i];
                    auto right=B->find(need);
                    if(right==B->end()) continue;
                    for(Word x:fixed.second) for(Word y:left.second) for(Word z:right->second) {
                        Word m=x|y|z;
                        if(canonical(m,perms,count)) out.push_back(m);
                    }
                }
            }
        }
        *result=new Word[out.size()];
        std::copy(out.begin(),out.end(),*result);
        return out.size();
    } catch (...) {return -1;}
}
