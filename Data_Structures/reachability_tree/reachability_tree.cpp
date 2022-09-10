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
 
#define N 600005
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
    (ch == '-')? minus = true: result = ch - '0';
    while (true) {
        ch = getchar();
        if (ch < '0' or ch > '9') break;
        result = (result << 3) + (result << 1) + (ch - '0');
    }
    if(minus) result = -result;
}

struct RT {
    ll id[N], values[N], be[N], en[N],  p[N][20], nodes, boc;
    vi adj[N];
    inline ll find(ll x) {
        while(x != id[x]) id[x] = id[id[x]], x = id[x];
        return x;
    }
    inline void unir(ll a, ll b, ll c) {
        ll p = find(a), q = find(b);
        id[nodes] = nodes;
        id[p] = id[q] = nodes;
        adj[nodes].pb(p);
        adj[p].pb(nodes);
        values[nodes] = c;
        if(p != q) adj[nodes].pb(q), adj[q].pb(nodes);
        nodes ++;
    }
    inline void dfs(ll u, ll pp) {
        be[u] = boc ++, p[u][0] = pp;
        FER(i, 1, 19) if(p[u][i - 1] != -1) p[u][i] = p[p[u][i - 1]][i - 1];
        for(auto xd : adj[u]) if(xd != pp) dfs(xd, u);
        en[u] = boc ++;
    }
    inline bool test(ll a, ll b) {
        if(a == -1) return true;
        return be[a] <= be[b] and en[a] >= en[b];   
    }
    inline ll lca(ll a, ll b) {
        if(test(a, b)) return a;
        if(test(b, a)) return b;
        IFR(i, 18, 0) if(!test(p[a][i], b)) a = p[a][i];
        return p[a][0];
    }
    inline void build(vector<tuple<ll, ll, ll>> &edges) {
    	boc = 0;
        FER(i, 0, nodes) id[i] = i, values[i] = 0;
        for(auto [c, a, b] : edges) unir(a, b, c);
        FER(i, 0, nodes) FER(j, 0, 19) p[i][j] = -1;
        dfs(nodes - 1, -1);
    }
}rt;

struct T {
    ii a, b;
    ll v;
    T(){}
    T(ii a, ii b, ll v) : a(a), b(b), v(v) {}
    inline void clear() {
        a = {INF, INF};
        b = {-INF, -INF};
        v = -1;
    }
    inline T Op(T x, T y) {
        if(x.v == 1) {
            if(y.v == 1) {
                auto xa = min(x.a, y.a);
                auto xb = max(x.b, y.b);
                return T(xa, xb, x.v);
            }
            return x;
        }
        if(y.v == 1) {
            if(x.v == 1) {
                auto xa = min(x.a, y.a);
                auto xb = max(x.b, y.b);
                return T(xa, xb, x.v);
            }
            return y;
        }
        T xd;
        xd.clear();
        return xd;
    }
};

struct ST {
    ll n, lazy[N << 2];
    T t[N << 2], act[N << 2];
    inline void updpro(ll laz, ll id, ll l, ll r) {
        if(laz != -1) {
        	T tz;
        	tz.clear();
            if(laz == 1) t[id] = act[id];
            else t[id] = tz;
            t[id].v = laz;
            lazy[id] = laz;
        }
    }
    inline void proh(ll id, ll l, ll r) {
        ll mid = (l + r) >> 1;
        updpro(lazy[id], id << 1, l, mid);
        updpro(lazy[id], id << 1 | 1, mid, r);
        lazy[id] = -1;
    }
    inline void Upd(ll x, ll y, ll val, ll id, ll l, ll r) {
        if(r <= x or y <= l) return ;
        if(x <= l and r <= y) {
            updpro(val, id, l, r);
            return;
        }
        proh(id, l, r);
        ll mid = (l + r) >> 1;
        Upd(x, y, val, id << 1, l, mid);
        Upd(x, y, val, id << 1 | 1, mid, r);
        t[id] = t[id].Op(t[id << 1], t[id << 1 | 1]);       
    }
    inline T Que(ll x, ll y, ll id, ll l, ll r) {
        if(r <= x or y <= l) { T xd; xd.clear(); return xd;}
        if(x <= l and r <= y) return t[id];
        proh(id, l, r);
        ll mid = (l + r) >> 1;
        auto L = Que(x, y, id << 1, l, mid);
        auto R = Que(x, y, id << 1 | 1, mid, r);
        return t[0].Op(L, R);
    }
    inline void Build(ll id, ll l, ll r) {
        if(l + 1 == r) {
            ii xa = {rt.be[l], l};
            ii yb = {rt.en[l], l};
            t[id] = T(xa, yb, 1);
            act[id] = t[id];
            return;
        }
        ll mid = (l + r) >> 1;
        Build(id << 1, l, mid);
        Build(id << 1 | 1, mid, r);
        t[id] = t[0].Op(t[id << 1], t[id << 1 | 1]);
        act[id] = t[id];
    }
    inline void upd(ll x, ll y, ll val) { Upd(x, y, val, 1, 0, n);}
    inline T que(ll x, ll y) { return Que(x, y, 1, 0, n);}
    inline void build() { FER(i, 0, n << 2) lazy[i] = -1; Build(1, 0, n);}
}st;

int main() {
    fastio;
    // https://codeforces.com/contest/1628/problem/E
    // Reachability Tree Tutorial: https://codeforces.com/blog/entry/85714
    ll n, q, ty, l, r; cin >> n >> q;
    vector<tuple<ll, ll, ll>> vec;
    FER(i, 0, n - 1) {
        ll a, b, c; cin >> a >> b >> c; a --, b --;
        vec.emplace_back(c, a, b);
    }
    sort(all(vec));
    rt.nodes = n;
    rt.boc = 0;
    rt.build(vec);
    st.n = (n << 1) - 1;
    st.build();
    auto dg = [&]() {
    	FER(i, 0, st.n) {
    		auto xd = st.que(i, i + 1);
    		auto [xs, a] = xd.a;
    		auto [xy, b] = xd.b;
    	}	
    };
    dg();
    st.upd(0, st.n, 0);
    auto Q = [&](ll x) {
        auto A = st.que(0, n);
        auto [tx, u] = A.a;
        auto [tz, v] = A.b;
        if(A.v != -1) {
            auto xx = u != x ? rt.values[rt.lca(u, x)] : -1;
            auto yy = v != x ? rt.values[rt.lca(v, x)] : -1;
            return max(xx, yy);   
        }
        return -1;
    };
    FER(i, 0, q) {
        cin >> ty;
        if(ty == 1) {
            cin >> l >> r; l --;
            st.upd(l, r, 1);
        }
        else if(ty == 2) {
            cin >> l >> r; l --;
            st.upd(l, r, 0);
        }
        else {
            cin >> l; l --;
            auto CB = Q(l);
            cout << CB << "\n";
        }
    }
    return 0;
}