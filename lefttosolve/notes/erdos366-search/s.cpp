// search consecutive cube-full numbers up to N = 10^E. n = a^3 * m, m = b^4 c^5, b,c squarefree coprime (unique).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned __int128 u128; typedef unsigned long long u64;
struct P { u128 m; u64 a; };
static void pr(u128 x){ char s[50]; int i=49; s[i]=0; if(!x) s[--i]='0'; while(x){ s[--i]='0'+(int)(x%10); x/=10;} printf("%s",s+i); }
static inline u64 red(u128 n){ const u64 M=0xFFFFFFFFFFFFFFC5ULL; u64 lo=(u64)n, x=(u64)(n>>64)*59; u64 s=lo+x; if(s<lo) s+=59; if(s>=M) s-=M; return s; }
int main(int argc,char**argv){
  int E=atoi(argv[1]); u64 t=argc>2?atoll(argv[2]):10000000ULL;
  u128 N=1; for(int i=0;i<E;i++) N*=10;
  u64 B=1; while((u128)(B+1)*(B+1)*(B+1)*(B+1)<=N) B++;
  vector<char> sf(B+1,1); for(u64 p=2;p*p<=B;p++) for(u64 q=p*p;q<=B;q+=p*p) sf[q]=0;
  vector<P> ps;
  for(u64 c=1;;c++){ u128 c5=(u128)c*c*c*c*c; if(c5>N) break; if(!sf[c]) continue;
    for(u64 b=1;b<=B;b++){ u128 b4=(u128)b*b*b*b; if(b4>N/c5) break; if(!sf[b]||__gcd(b,c)!=1) continue; ps.push_back({b4*c5,1}); } }
  sort(ps.begin(),ps.end(),[](const P&x,const P&y){return x.m<y.m;});
  fprintf(stderr,"pairs %zu\n",ps.size());
  vector<u64> v, tmp; u64 total=0; u64 prevlast=0; bool have=false; u64 cand=0;
  vector<u128> full; bool keep = E<=12;
  for(u64 k=1;;k++){ u128 H=(u128)(k*t)*(k*t)*(k*t); bool last=false; if(H>N){H=N+1; last=true;}
    v.clear();
    for(auto &p:ps){ if(p.m>=H) break; u64 a=p.a; for(;;){ u128 n=(u128)a*a*a*p.m; if(n>=H) break; v.push_back(red(n)); if(keep) full.push_back(n); a++; } p.a=a; }
    // radix sort
    size_t n=v.size(); tmp.resize(n);
    for(int pass=0;pass<8;pass++){ size_t cnt[257]={0}; int sh=pass*8; for(size_t i=0;i<n;i++) cnt[((v[i]>>sh)&255)+1]++; for(int i=0;i<256;i++) cnt[i+1]+=cnt[i]; for(size_t i=0;i<n;i++) tmp[cnt[(v[i]>>sh)&255]++]=v[i]; v.swap(tmp); }
    for(size_t i=0;i+1<n;i++) if(v[i+1]-v[i]<=1){ cand++; printf("CAND seg %llu low64 %llu %llu H=",(unsigned long long)k,v[i],v[i+1]); pr(H); printf("\n"); }
    total+=n;
    if(k%20==0||last){ fprintf(stderr,"seg %llu total %llu upto ",(unsigned long long)k,total); u128 x=H; char s[50]; int i=49; s[i]=0; while(x){ s[--i]='0'+(int)(x%10); x/=10;} fprintf(stderr,"%s\n",s+i); fflush(stdout);}    
    if(last) break; }
  printf("DONE E=%d total cubefull<=N: %llu cand %llu\n",E,total,cand);
  if(keep){ sort(full.begin(),full.end()); for(size_t i=0;i+1<full.size();i++) if(full[i+1]-full[i]<=1){printf("FULLCAND ");pr(full[i]);printf("\n");} }
}
