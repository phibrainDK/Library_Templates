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


typedef long long ll;
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

vi g[1 << 19], stree[1 << 19], rg[1 << 19], bucket[1 << 19];
ll sdom[1 << 19], par[1 << 19], dom[1 << 19], dsu[1 << 19], label[1 << 19];
ll arr[1 << 19], rev[1 << 19], T;
ll vis[1 << 19], p[1 << 19], be[1 << 19], en[1 << 19], boc;
 
inline void dfs0(ll u){
    T++; arr[u] = T; rev[T] = u;
    label[T] = T; sdom[T] = T;dsu[T] = T;
    for(auto w: g[u]){
        if(!arr[w]){
            dfs0(w);
            par[arr[w]] = arr[u];
        }
        rg[arr[w]].pb(arr[u]);
    }
}
inline ll Find(ll u, ll x = 0){
    if(u == dsu[u])return x ? -1 : u;
    ll v = Find(dsu[u], x + 1);
    if(v < 0) return u;
    if(sdom[label[dsu[u]]] < sdom[label[u]]) label[u] = label[dsu[u]];
    dsu[u] = v;
    return x ? v :label[u];
}
inline void Union(ll u,ll v) { dsu[v]=u;}
inline void bfs(ll u){
    vis[u]++;
    be[u] = boc++;
    for(auto xd: stree[u]) if(!vis[xd]){
        bfs(xd);
        p[xd] = u;
    }
    en[u] = boc++;
}
 
 
int main(){
    fastio;
    // https://codeforces.com/gym/100513/problem/L
    ll n, m; 
    while(cin >> n >> m){
        boc = 1;
        T = 0;
        vii edges;
        FER(i, 0, m){
            ll a, b; cin >> a >> b;
            g[a].pb(b);
            edges.pb({a, b});
        }
        auto Lengauer_Tarjan = [&](ll x){
            dfs0(x);
            IFR(i, n, 1){
                if(!sdom[i]) continue;
                for(auto xd: rg[i]) sdom[i] = min(sdom[i], sdom[Find(xd)]);
                if(i > 1) bucket[sdom[i]].pb(i);
                for(auto xd: bucket[i]){
                    auto v = Find(xd);
                    if(sdom[v] == sdom[xd]) dom[xd] = sdom[xd];
                    else dom[xd] = v;
                }
                if(i > 1) Union(par[i], i);
            }
            FER(i, 2, n + 1){
                if(!sdom[i] or !dom[i]) continue;
                if(dom[i] != sdom[i]) dom[i] = dom[dom[i]];
                stree[rev[i]].pb(rev[dom[i]]);
                stree[rev[dom[i]]].pb(rev[i]);
            }
            bfs(1);
        };
        auto test = [&](ll a, ll b){
            if(!be[a] or !be[b]) return true;
            return be[a] <= be[b] and en[a] >= en[b];
        };
        Lengauer_Tarjan(1);
        vi tnt;
        FER(i, 0, sz(edges)){
            auto [a, b] = edges[i];
            if(!test(b, a)){
                tnt.pb(i + 1);
            }
        }
        cout << sz(tnt) << "\n";
        for(auto xd: tnt) cout << xd << " "; cout << "\n";
        FER(i, 0, n + T + 1){
            vi().swap(g[i]);
            vi().swap(stree[i]);
            vi().swap(rg[i]);
            vi().swap(bucket[i]);
            sdom[i] = par[i] = dom[i] = dsu[i] = 0;
            label[i] = arr[i] = rev[i] = vis[i] = 0;
            be[i] = en[i] = 0;
        }
    }
    return 0;
}