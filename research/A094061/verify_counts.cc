#include <gmpxx.h>
#include <array>
#include <iostream>
#include <vector>
#include <map>
#include <algorithm>
using namespace std;
struct Test {int hi, p, k; unsigned long pk, mod, low=0;};
int main(int argc,char** argv) {
  int N=argc>1?atoi(argv[1]):50000;
  vector<vector<int>> start(N+1), finish(N+1); vector<Test> tests;
  vector<bool> prime(N+1,true);
  for(int p=2;p<=N;p++) if(prime[p]) {
    for(long a=2L*p;a<=N;a+=p) prime[a]=false;
    if(p<5) continue;
    for(long pk=p,k=1;pk<=N;pk*=p,k++) for(int m=1;m<=N/pk;m++) if(m%p) {
      int hi=m*pk; start[hi/p].push_back(tests.size());finish[hi].push_back(tests.size());
      tests.push_back({hi,p,int(k),(unsigned long)pk,(unsigned long)(pk*pk*p),0});
    }
  }
  mpz_class a0=0,a1=0,a2=0,a3=1,x;
  map<int,pair<int,int>> byDepth; map<int,int> firstSharp;
  vector<unsigned long> initial;
  for(long n=0;n<=N;n++) {
    if(n<12) initial.push_back(a3.get_ui());
    for(auto i:start[n]){auto &t=tests[i];t.low=mpz_fdiv_ui(a3.get_mpz_t(),t.mod);}
    for(auto i:finish[n]) {
      auto &t=tests[i];auto hi=mpz_fdiv_ui(a3.get_mpz_t(),t.mod); long d=long(hi)-long(t.low);
      if (d%long(t.pk*t.pk)!=0) {cout<<"failure n="<<n<<" p="<<t.p<<" v="<<t.k<<" difference mod "<<t.mod<<"="<<d<<endl;return 1;}
      byDepth[t.k].first++;
      if(d) {byDepth[t.k].second++; if(!firstSharp.count(t.p)) firstSharp[t.p]=n;}
    }
    if(n==N) break;
    x=n*(5*n+1)*a3+2*(15*n*n+6*n-5)*a2-8*(5*n*n-23*n+21)*a1-64*(n-2)*(n-2)*a0;
    if(!mpz_divisible_ui_p(x.get_mpz_t(),(n+1)*(n+1))){cout<<"Inexact division at "<<n<<endl;return 2;}
    mpz_divexact_ui(x.get_mpz_t(),x.get_mpz_t(),(n+1)*(n+1));swap(a0,a1);swap(a1,a2);swap(a2,a3);swap(a3,x);
  }
  cout<<"prefix";for(auto i:initial) cout<<" "<<i;cout<<"\nthrough "<<N<<", "<<tests.size()<<" primitive triples\n";
  for(auto [k,c]:byDepth)cout<<"k="<<k<<" passed="<<c.first<<" exact order="<<c.second<<"\n";
  cout<<"first sharp multiples of small primes:";
  for(int p=5;p<=110;p++) if(prime[p]) cout<<" "<<p<<"->"<<firstSharp[p];
  cout<<endl;
}
