// Exhaust all C(21,9)=293930 normalized 11-digit alphabets over F23.
#include <bits/stdc++.h>
using namespace std;
int main(int argc,char**argv){
 if(argc!=2)return 2;
 ifstream f(argv[1]);if(!f)return 2;
 set<unsigned long long> cuts;string s;int count=0;
 while(getline(f,s)){
  if(s.empty()||s[0]=='#')continue;
  auto p=s.find(':');if(p==string::npos)return 2;
  vector<int> D;stringstream v(s.substr(p+1));string tok;
  while(getline(v,tok,',')){int x=stoi(tok);if(x<0||x>=23)return 2;D.push_back(x);}
  for(int a=1;a<23;++a)for(int b=0;b<23;++b){
   unsigned long long m=0;for(int x:D)m|=1ULL<<((a*x+b)%23);
   if(__builtin_popcountll(m)!=(int)D.size())return 2;
   cuts.insert(m);
  }
  count++;
 }
 if(count!=22)return 2;
 unsigned long long total=0,missing=0;
 for(unsigned long long c=0;c<(1ULL<<21);++c){
  if(__builtin_popcountll(c)!=9)continue;
  unsigned long long d=(c<<2)|3ULL;total++;
  bool blocked=false;for(auto m:cuts)if((m&d)==m){blocked=true;break;}
  if(!blocked){missing++;cerr<<"UNCOVERED "<<d<<"\n";}
 }
 cout<<"EXACT_COVERAGE normalized="<<total<<" uncovered="<<missing
     <<" motifs="<<count<<" orbit_cuts="<<cuts.size()<<"\n";
 return total==293930&&missing==0?0:1;
}
