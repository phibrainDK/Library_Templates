// #################################################################################################
// #                                        You told me                                            #
// #           At your absolute best, you still won't be good enough for the wrong person          #
// #                   At your worst, you'll still be worth it to the right person                 #
// #                           It was good while it lasted, good bye                               #
// #    I believe I really loved you... to that point that I always wanted to hear your voice      #
// #    But before my hand could reach you... you seem to be slowly disappearing from my sight     #
// #################################################################################################


// #pragma GCC optimize ("Ofast,unroll-loops")
// #pragma GCC target ("sse,sse2,sse3,ssse3,sse4,popcnt,abm,mmx,avx,tune=native")

#include <bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>

#define pb push_back
#define ff  first
#define ss second
#define tm1 first
#define tm2 second.first
#define tm3 second.second
#define sz(x) ll(x.size())
#define fill(x, v) memset(x, v, sizeof(x))
#define all(v) (v).begin(), (v).end()
#define FER(i,a,b) for(ll i=ll(a); i< ll(b); ++i)
#define IFR(i,a,b) for(ll i=ll(a); i>=ll(b); i-- )
#define fastio ios_base::sync_with_stdio(0); cin.tie(0)

// #define N 6800005
#define mod1 1000000007
// #define mod1 998244353
#define mod2 1000000009
#define bas 987625403
#define sqr(x) 1LL * (x) * (x)
#define INF (ll) 1e9

using namespace std;
using namespace __gnu_pbds;


typedef long long  ll;
typedef pair<ll, ll> ii;
typedef pair<ii, ll> tri;
typedef vector<ll> vi;
typedef vector<ii> vii;
typedef tree<int, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update> S_t;
mt19937_64 rng(chrono::steady_clock::now().time_since_epoch().count());
struct custom_Hash {
    static uint64_t splitmix64(uint64_t x) {
        x += 0x9e3779b97f4a7c15;
        x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;
        x = (x ^ (x >> 27)) * 0x94d049bb133111eb;
        return x ^ (x >> 31);
    }
    size_t operator()(uint64_t x) const {
        static const uint64_t FIXED_RANDOM = chrono::steady_clock::now().time_since_epoch().count();
        return splitmix64(x + FIXED_RANDOM);
    }
};

#define trace(...) fff(#__VA_ARGS__, __VA_ARGS__)
template<typename t> void fff(const char* x, t&& val1) { cout << x << " : " << val1 << "\n";}
template<typename t1, typename... t2> void fff(const char* x, t1&& val1, t2&&... val2){
    const char* xd = strchr(x + 1, ',');
    cout.write(x, xd - x) << " : " <<val1 << " | ";
    fff(xd + 1, val2...);
}

inline ll add(ll a, ll b, ll mod) { return a + b < mod? a + b : a + b - mod;}
inline ll rem(ll a, ll b, ll mod) { return a >= b ? a - b : a - b + mod;}
inline ll mul(ll a, ll b, ll mod) { return 1LL * a * b % mod;}
inline void Mul(ll &a, ll b, ll mod) { a = 1LL * a * b % mod;}
inline ll bp(ll a, long long p, ll mod){
    ll ret;
    for(ret = 1; p; p >>= 1, Mul(a, a, mod)) (p & 1) && (Mul(ret, a, mod), 1);
    return ret;
}

static inline void read(ll &result) {
    bool minus = false;
    char ch;
    ch = getchar();
    while (true) {
        if (ch == '-') break;
        if (ch >= '0' and ch <= '9') break;
        ch = getchar();
    }
    (ch == '-') ? minus = true: result = ch - '0';
    while (true) {
        ch = getchar();
        if (ch < '0' or ch > '9') break;
        result = (result << 3) + (result << 1) + (ch - '0');
    }
    if(minus) result = -result;
}

inline ll G(char s){
	if(s >= 'a' and s <= 'z') return s - 'a';
	if(s >= 'A' and s <= 'Z') return s - 'A' + 26;
	return s - '0' + 52;
}
 
inline char F(ll x){
	if(x < 26) return char(x + 'a');
	if(x < 52) return x -= 26, char(x + 'A');
	x -= 52;
	return char (x + '0');
}
 
ll in[1 << 19], out[1 << 19];
vi adj[1 << 17], tnt;
 
inline void dfs(ll u){
	while(sz(adj[u])){
		auto it = adj[u].back();
		adj[u].pop_back();
		dfs(it);
	}
	tnt.pb(u % 63);
}
 
int main(){
    // https://codeforces.com/contest/508/problem/D
	fastio;
	ll n; cin>>n;
	FER(i, 0, n){
		string s; cin>>s;
		ll x = G(s[1]) + G(s[0]) * 63;
		ll y = G(s[2]) + G(s[1]) * 63;
		adj[x].pb(y);
		out[x] ++, in[y] ++;
	}
	ll a = -1, b = -1, flag = 0;
	FER(i, 0, sqr(63)){
		if(out[i] == in[i]) {
			if(in[i]) a = i;
			continue;
		}
		if(in[i] - out[i] == 1 or out[i] - in[i] == 1){
			flag ++;
			if(out[i] - in[i] == 1){
				b = i;
			}
		}
		else{
			cout << "NO\n";
			return 0;
		}
	}
	if(flag == 0){
		dfs(a);
		reverse(all(tnt));
		if(sz(tnt) != n + 1) return cout << "NO\n", 0;
		cout << "YES\n";
		cout << F(a/63);
		for(auto xd: tnt) cout << F(xd % 63);
		cout << "\n";
	}
	else if (flag == 2){
		dfs(b);
		reverse(all(tnt));
		if(sz(tnt) != n + 1) return cout << "NO\n", 0;
		cout << "YES\n";
		cout << F(b/63);
		for(auto xd: tnt) cout << F(xd%63);
		cout << "\n";
	}
	else{
		cout << "NO\n";
	}
	return 0;
}