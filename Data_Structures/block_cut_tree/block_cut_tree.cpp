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
 
#define N 300005
#define mod1 1000000007
// #define mod1 998244353
#define mod2 1000000009
#define bas 987625403
#define sqr(x) 1LL * (x) * (x)
#define INF (ll) 2e9
 
using namespace std;
using namespace __gnu_pbds;
 
 
typedef int ll;
typedef pair<ll, ll> ii;
typedef pair<ll, ii> tri;
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
inline ll rem(ll a, ll b, ll mod) { return a >= b? a - b: a - b + mod;}
inline ll mul(ll a, ll b, ll mod) { return (long long) a * b % mod;}
inline void Mul(ll &a, ll b, ll mod) { a = (long long) a * b % mod;}
inline ll bp(ll a, ll p, ll mod){
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
    (ch == '-')? minus = true: result = ch - '0';
    while (true) {
        ch = getchar();
        if (ch < '0' or ch > '9') break;
        result = (result << 3) + (result << 1) + (ch - '0');
    }
    if(minus) result = -result;
}
 
multiset<ll> s[1 << 19];
 
struct ST{
	ll n, t[1<<20];
	inline ll Op(ll &a, ll &b) { return min(a, b);}
	inline void build(ll m) { n = m; FER(i, 1, n << 1) t[i] = INF;}
	inline void modify(ll p, ll val) { for(t[p += n] = val; p >>= 1; ) t[p]=Op(t[p << 1], t[p << 1 | 1]);}
	inline ll que(ll l, ll r){
		ll ans = INF;
		for(l += n, r += n; l < r; l >>= 1, r >>= 1){
			if(l & 1) ans=min(ans, t[l ++]);
			if(r & 1) ans=min(t[-- r], ans);
		}
		return ans;
	}
}st;
 
 
ll dfn[1 << 19], low[1 << 19], path[1 << 19];
ll wei[1 << 19], boc, tot, bcc;
vi adj[1 << 19], graph[1 << 19];
 
ll rt[1 << 19], id[1 << 19], p[1 << 19], d[1 << 19], tsz[1 << 19], gid;
 
inline void dfs(ll u, ll pp, ll depth){
	tsz[u] = 1, p[u] = pp, d[u] = depth;
	for(auto xd: adj[u]) if(xd != pp) 
		dfs(xd, u, depth + 1), tsz[u] += tsz[xd];
}
 
inline void go(ll u, ll root){
	id[u] = gid++, rt[u] = root;
	ll w = -1, bc = 0;
	for(auto xd: adj[u]) if(xd != p[u] and tsz[xd] > w) w = tsz[xd], bc = xd;
	if(bc) go(bc, root);
	for(auto xd: adj[u]) if(xd != p[u] and xd != bc) go(xd, xd);
}
 
inline ll Que(ll a, ll b, ll n){
	ll ans = INF;
	while(rt[a] != rt[b]){
		if(d[rt[a]] > d[rt[b]]) swap(a, b);
		ans = min(ans, st.que(id[rt[b]], id[b] + 1));
		b = p[rt[b]];
	}
	if(d[a] > d[b]) swap(a, b);
	ans = min(ans, st.que(id[a], id[b] + 1));
	if(a >= n) ans = min(ans, wei[p[a]]);
	return ans;
}
 
 
inline void Tarjan(ll u, ll pp){
	dfn[u] = low[u] = boc++;
	path[tot ++] = u;
	for(auto xd: adj[u]) {
		if(xd == pp) continue;
		if(dfn[xd] == -1){
			Tarjan(xd, u);
			low[u] = min(low[u], low[xd]);
			if(low[xd] >= dfn[u]){
				while(1){
					ll cur=path[tot - 1];
					graph[cur].pb(bcc);
					graph[bcc].pb(cur);
					s[bcc].insert(wei[cur]);
					tot --;
					if(cur == xd) break;
				}
				graph[u].pb(bcc);
				graph[bcc].pb(u);
				s[bcc].insert(wei[u]);
				bcc++;
			}
		}
		else if(dfn[xd] < dfn[u]) low[u]=min(low[u], dfn[xd]);
	}
}
 
 
int main(){
    // https://codeforces.com/contest/487/problem/E
	fastio;
	ll n, m, q, a, b; cin >> n >> m >> q;
	bcc = n;
	FER(i, 0, n) cin >> wei[i];
	FER(i, 0, m){
		cin >> a >> b; a--, b--;
		adj[a].pb(b);
		adj[b].pb(a);
	}
	fill(dfn, -1);
	Tarjan(0, -1);
	FER(i, 0, bcc) {
		adj[i].clear();
		adj[i] = graph[i];
	}
	dfs(0, -1, 0);
	go(0, 0);
	st.build(bcc);
	FER(i, 0, n) st.modify(id[i], wei[i]);
	FER(i, n, bcc){
		s[i].insert(INF);
		if(p[i] != -1) s[i].erase(s[i].lower_bound(wei[p[i]]));
		st.modify(id[i], *s[i].begin());
	}
	FER(i, 0, q){
		char ty;
		cin >> ty >> a >> b; a --;
		if(ty == 'C'){
			if(p[a] != -1) s[p[a]].erase(s[p[a]].lower_bound(wei[a]));
			wei[a] = b;
			if(p[a] != -1){
				s[p[a]].insert(wei[a]);
				st.modify(id[p[a]], *s[p[a]].begin());
			}
			st.modify(id[a], wei[a]);
		}
		else{
			b --;
			auto ans = Que(a, b, n);
			cout << ans << "\n";
		}
	}
	return 0;
}