// Regenerate the 1,016 isometry classes of independent 33-sets in C7^3.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <unordered_map>
#include <vector>

using Mask = std::uint64_t;
using Layers = std::array<Mask, 7>;
using Pattern = std::array<int, 7>;
using Point = std::array<int, 3>;
constexpr Mask full = (Mask{1} << 49) - 1;
int wrap(int x) { return (x+14) % 7; }
int size(Mask x) { return __builtin_popcountll(x); }
Mask cell(int y, int z) { return Mask{1} << (7*wrap(y)+wrap(z)); }
std::array<Mask, 49> near;
Mask neighborhood(Mask x) {
    Mask result = 0;
    while (x) {
        result |= near[__builtin_ctzll(x)];
        x &= x-1;
    }
    return result;
}

template<typename Visit>
void subsets(Mask allowed, int need, Mask chosen, const Visit& visit) {
    if (!need) { visit(chosen); return; }
    while (size(allowed) >= need) {
        int i = __builtin_ctzll(allowed);
        Mask site = Mask{1} << i;
        allowed ^= site;
        subsets(allowed & ~near[i], need-1, chosen | site, visit);
    }
}

struct Motion {
    bool swap;
    int sign_y, sign_z, dy, dz;
    Mask move(int y, int z) const {
        if (swap) std::swap(y,z);
        return cell(y*sign_y+dy, z*sign_z+dz);
    }
};
std::map<Mask,std::vector<Motion>> normalizers;
std::set<Mask> planar_reps;
std::unordered_map<Mask,std::vector<Mask>> full_completions;
int available[7][128][128];

void prepare_plane() {
    for (int y=0; y<7; ++y) for (int z=0; z<7; ++z)
        for (int a=-1; a<=1; ++a) for (int b=-1; b<=1; ++b)
            near[7*y+z] |= cell(y+a,z+b);
    bool eleven_exists = false;
    subsets(full,11,0,[&](Mask) { eleven_exists = true; });
    assert(!eleven_exists);
    std::vector<Motion> motions;
    for (bool swap : {false,true}) for (int sy : {-1,1}) for (int sz : {-1,1})
        for (int dy=0; dy<7; ++dy) for (int dz=0; dz<7; ++dz)
            motions.push_back({swap,sy,sz,dy,dz});
    subsets(full,10,0,[&](Mask ten) {
        Mask least = full;
        std::vector<Motion> best;
        for (auto op : motions) {
            Mask im=0;
            for (Mask s=ten; s; s&=s-1) {
                int i=__builtin_ctzll(s);
                im |= op.move(i/7,i%7);
            }
            if (im < least) { least=im; best.clear(); }
            if (im == least) best.push_back(op);
        }
        normalizers[ten]=best;
        planar_reps.insert(least);
        for (Mask s=ten; s; s=(s-1)&ten)
            if (size(s)>=3) full_completions[s].push_back(ten^s);
    });
    assert(normalizers.size()==980 && planar_reps.size()==3);

    // Maximum number that can fit in k consecutive free rows between the
    // indicated two boundary rows of a planar independent set.
    std::vector<int> rows;
    std::array<int,128> blocked{};
    for (int r=0; r<128; ++r) {
        int right=((r<<1)|(r>>6))&127;
        blocked[r]=r|right|(r>>1)|((r&1)<<6);
        if (!(r&right)) rows.push_back(r);
    }
    for (int a:rows) for (int b:rows) available[0][a][b]=(blocked[a]&b)?-100:0;
    for (int k=1; k<=6; ++k) for (int a:rows) for (int b:rows) {
        int best=-100;
        for (int r:rows) if (!(r&blocked[b]))
            best=std::max(best,size(r)+available[k-1][a][r]);
        available[k][a][b]=best;
    }
}

std::map<Layers,int> atlas;
void record(const Layers& layers) {
    std::vector<Point> points;
    for (int x=0; x<7; ++x) for (Mask m=layers[x]; m; m&=m-1) {
        int i=__builtin_ctzll(m);
        points.push_back({x,i/7,i%7});
    }
    assert(points.size()==33);
    Layers best;
    best.fill(full);
    int stabilizer=0;
    // Normalize any ten-window on any axis. Equal canonical images count the
    // stabilizer, since two motions yielding the same image differ by one.
    for (int a=0; a<3; ++a) for (int sign:{-1,1}) for (int start=0; start<7; ++start) {
        int b=(a+1)%3, c=(a+2)%3;
        Mask ten=0;
        for (auto p:points) if (wrap(sign*(p[a]-start))<2) ten |= cell(p[b],p[c]);
        auto it=normalizers.find(ten);
        if (it==normalizers.end()) continue;
        for (auto op:it->second) {
            Layers im{};
            for (auto p:points) im[wrap(sign*(p[a]-start))] |= op.move(p[b],p[c]);
            if (im<best) { best=im; stabilizer=0; }
            if (im==best) ++stabilizer;
        }
    }
    constexpr int group=6*14*14*14;
    assert(stabilizer && group%stabilizer==0);
    auto entry=atlas.emplace(best,group/stabilizer);
    assert(entry.first->second==group/stabilizer);
}

struct Margins {
    std::array<int,14> first{}, count{};
};
class Enumeration {
    int target;
    Pattern deficit{}, populations{};
    Layers layers{};

    bool update(int k, Mask layer, Margins& totals) {
        if (k==6 && (neighborhood(layer)&layers[0])) return false;
        int rows[2][7]{};
        for (Mask m=layer; m; m&=m-1) {
            int i=__builtin_ctzll(m);
            rows[0][i/7] |= 1<<(i%7);
            rows[1][i%7] |= 1<<(i/7);
        }
        for (int a=0; a<2; ++a) {
            int bound=0;
            for (int j=0; j<7; ++j) {
                int t=7*a+j, row=rows[a][j]|rows[a][(j+1)%7];
                if (k==0) totals.first[t]=row;
                totals.count[t]+=size(row);
                bound+=totals.count[t]+available[6-k][totals.first[t]][row];
            }
            // On each transverse axis the seven projected window sizes sum to twice the target.
            if (bound<2*target) return false;
        }
        layers[k]=layer;
        return true;
    }

    void advance(int k,const Margins& previous) {
        if (k==7) { assert(target==33); record(layers); return; }
        auto visit=[&](Mask layer) {
            Margins totals=previous;
            if (update(k,layer,totals)) advance(k+1,totals);
        };
        Mask last=layers[k-1];
        if (deficit[k-1]==0) {
            auto it=full_completions.find(last);
            if (it!=full_completions.end()) for (Mask next:it->second) visit(next);
        } else {
            Mask allowed=full & ~neighborhood(last);
            if (k==6) allowed &= ~neighborhood(layers[0]);
            subsets(allowed,populations[k],0,visit);
        }
    }

    void run_pattern() {
        // Choose the least dihedral image of the seven deficits. It starts
        // with a zero, since the nonnegative deficits sum to at most four.
        for (int i=0; i<7; ++i) for (int sign:{-1,1}) {
            Pattern image;
            for (int j=0; j<7; ++j) image[j]=deficit[wrap(i+sign*j)];
            if (image<deficit) return;
        }
        for (int i=0; i<7; ++i)
            populations[i]=target-30+deficit[(i+1)%7]+deficit[(i+3)%7]+deficit[(i+5)%7];
        for (Mask ten:planar_reps) for (Mask a=ten; a; a=(a-1)&ten) {
            if (size(a)!=populations[0]) continue;
            Margins totals;
            if (update(0,a,totals) && update(1,ten^a,totals)) advance(2,totals);
        }
    }

public:
    explicit Enumeration(int size) : target(size) {}
    void choose(int k,int left) {
        if (k==7) { if (!left) run_pattern(); return; }
        for (int d=0; d<=left; ++d) { deficit[k]=d; choose(k+1,left-d); }
    }
};

int main() {
    prepare_plane();
    Enumeration exclude34(34);
    exclude34.choose(0,2);
    Enumeration search(33);
    search.choose(0,4);
    int total=0;
    for (const auto& entry:atlas) {
        for (int k=0; k<7; ++k) std::cout << (k?"\t":"") << entry.first[k];
        std::cout << '\n';
        total+=entry.second;
    }
    assert(atlas.size()==1016 && total==16672544);
    return 0;
}
