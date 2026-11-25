// Integer upper enclosure of wave_independent.py's translated polygon overlaps.
// Input: half-angle bin count, x, then two ordered tables of (height, width).
#include <algorithm>
#include <cassert>
#include <iostream>
#include <vector>
using I = __int128_t;
using L = long long;
using P = std::pair<L,L>;
constexpr L S=1000000000000LL,H=S/2;
using Table=std::vector<P>;
I ceildiv(I a,I b) { assert(b>0); return a>=0?(a+b-1)/b:a/b; }
std::string decimal(I a) {
 if(a<10)return std::string(1,'0'+int(a));
 return decimal(a/10)+char('0'+int(a%10));
}
Table table() {
 size_t n;std::cin>>n;Table g(n);for(auto& [z,x]:g)std::cin>>z>>x;
 assert(std::is_sorted(g.begin(),g.end())&&g.front().first==0&&g.back().first==H);
 return g;
}
L at(const Table& g,L z,int sign,size_t& i) {
 while(i+1<g.size() && g[i+1].first<=z)++i;
 auto [y,w]=g[i];if(y==z)return sign*w;
 assert(y<z && i+1<g.size());
 auto [t,v]=g[i+1];return sign*w+ceildiv(I(sign)*(v-w)*(z-y),t-y);
}
I overlap(L dx,L dl,L dh,const Table& left,const Table& right,L maxR) {
 if(dx>=maxR||dl>=H)return 0;
 Table fold;
 for(auto [z,w]:left)if(z<=H/2)fold.emplace_back(z+dl,w);
 for(auto [z,w]:left)if(z>=H/2)fold.emplace_back(z+dh,w);
 size_t i=0,j=0;L z=dl,prev=at(right,z,1,i)+at(fold,z,-1,j)-dx;
 I total=0;
 while(z<H) {
   L end=std::min(H,right[i+1].first);
   if(j+1<fold.size())end=std::min(end,fold[j+1].first);
   assert(end>z);
   L now=at(right,end,1,i)+at(fold,end,-1,j)-dx;
   L a=std::min(now,prev),b=std::max(now,prev);
   if(b>0)total+=a>=0?I(a+b)*(end-z):ceildiv(I(b)*b*(end-z),b-a);
   z=end;prev=now;
 }
 return total;
}
int main() {
 L N,x;std::cin>>N>>x;auto left=table(),right=table();L maxR=0;
 for(auto [z,w]:right)maxR=std::max(maxR,w);
 assert(N>=4096&&N<=1000000000 && N%4096==0);
 auto area=[&](L i,L j){
   I n2=I(N)*N,a=n2+I(i)*i,b=n2+I(j)*j;
   L xlo=(n2-I(j)*j)*S/b,xhi=ceildiv((n2-I(i)*i)*S,a);
   L ylo=I(2)*S*N*i/a,yhi=ceildiv(I(2)*S*N*j,b);
   L dl=std::max({0LL,3*S/4-yhi,ylo-3*S/4}),dh=std::max(3*S/4-ylo,yhi-3*S/4);
   return overlap(xlo,ylo,yhi,left,right,maxR)+overlap(2*x-xhi,dl,dh,left,right,maxR);
 };
 I total=0;
 for(L i=0;i<N;i+=N/4096) {
   if(area(i,i+N/4096)==0)continue;
   for(L j=i;j<i+N/4096;++j)
     total+=ceildiv(area(j,j+1)*N,I(N)*N+I(j)*j);
 }
 std::cout<<decimal(total)<<"\n";
}
