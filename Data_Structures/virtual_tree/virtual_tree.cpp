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
#define mod2 1000000009LL
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
    (ch == '-')? minus = true: result = ch-'0';
    while (true) {
        ch = getchar();
        if (ch < '0' or ch > '9') break;
        result = (result<<3)+ (result<<1) + (ch - '0');
    }
    if(minus) result = -result;
}

vi adj[1 << 17], graph[1 << 17];
ll dp[1 << 17][301], p[1 << 17][17], be[1 << 17], en[1 << 17], vis[1 << 17], cnt[1 << 17], ord[1 << 17], boc;
inline void dfs(ll u, ll pp) {
    p[u][0] = pp, be[u] = boc ++;
    FER(i, 1, 17) if(p[u][i - 1] != -1) p[u][i] = p[p[u][i - 1]][i - 1];
    for(auto xd : adj[u]) if(xd != pp) {
        dfs(xd, u);
    }
    en[u] = boc ++;
}
inline bool test(ll a, ll b) {
    if(a == -1) return true;
    return be[a] <= be[b] and en[a] >= en[b];
}
inline ll lca(ll a, ll b) {
    if(test(a, b)) return a;
    if(test(b, a)) return b;
    IFR(i, 16,  0) if(!test(p[a][i], b)) a = p[a][i];
    return p[a][0];
}

int main() {
    // https://codeforces.com/contest/1111/problem/E
    fastio;
    ll n, q; cin >> n >> q;
    FER(i, 0, n - 1) {
        ll a, b; cin >> a >> b; a --, b --;
        adj[a].pb(b);
        adj[b].pb(a);
    }
    dfs(0, -1);
    function<void(ll, ll)> bfs = [&](ll u, ll pp) {
        ord[u] = boc ++;
        for(auto xd : graph[u]) if(xd != pp) {
            cnt[xd] = cnt[u] + vis[xd];
            bfs(xd, u);
        }
    };
    auto Samantha = [&](ll root, vi &vec, ll m) {
        vi st;
        // virtual tree (after inorder dfs custom sort)
        for(auto xd : vec) {
            while(sz(st)) {
                auto u = st.back();
                if(test(u, xd)) {
                    graph[u].pb(xd);
                    graph[xd].pb(u);
                    break;
                }
                st.pop_back();
            }
            st.pb(xd);
        }
        cnt[root] = vis[root];
        boc = 0;
        bfs(root, -1);
        sort(all(vec), [&](ll a, ll b) {
            return ord[a] < ord[b];
        });
        vi tnt;
        for(auto xd : vec) if(vis[xd]) tnt.pb(xd);
        FER(i, 0, sz(tnt) + 1) FER(j, 1, m + 1) dp[i][j] = 0;
        dp[0][0] = 1;
        FER(i, 1, sz(tnt) + 1) {
            FER(j, 1, m + 1) {
                dp[i][j] = add(mul(dp[i - 1][j], (max(j - cnt[tnt[i - 1]] + 1, 0)), mod1), dp[i - 1][j - 1], mod1);
            }  
        }
        ll ans = 0;
        FER(i, 1, m + 1) ans = add(ans, dp[sz(tnt)][i], mod1);
        for(auto xd : vec) vi().swap(graph[xd]);
        return ans;
    };
    FER(i, 0, q) {
        ll k, m, r; cin >> k >> m >> r; r --;
        vi vec(k), tnt;
        for(auto &xd : vec) cin >> xd, xd --, vis[xd] ++, tnt.pb(xd);
        vec.pb(r);
        sort(all(vec), [&](ll a, ll b) {
            return be[a] < be[b];
        });
        FER(ij, 1, k + 1) vec.pb(lca(vec[ij - 1], vec[ij]));
        sort(all(vec)), vec.erase(unique(all(vec)), vec.end()); 
        sort(all(vec), [&](ll a, ll b) {
            return be[a] < be[b];
        });
        for(auto xd : vec) cnt[xd] = 0;
        auto CB = Samantha(r, vec, m);
        cout << CB << "\n";
        for(auto xd : tnt) vis[xd] = 0;
    }
    return 0;
}