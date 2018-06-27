#include <iostream>
#include <vector>
#include <cmath>
#include <stack>
using namespace std;
int a,a10;
string b;
stack < int > s;
void pre(){
    for(int i=0;i<b.size();i++) s.push(b[i]-48);
}
long long getLastDig(){
    long long res;
    if(s.empty()) return 1;
    int c= s.top(); s.pop();
    res=pow(a,c);
    cout<<res<<endl;
    res= res%10;
    res*= (long long) pow(getLastDig(),10)%10;
    res= res%10;
    return res;
}
int main() {
    int c;
	cin>>c;
	for(long i =0; i<c;i++){
		cin>>a>>b;
		a= a%10;
		pre();
		cout<<getLastDig()<<endl;
	}
	return 0;
}

