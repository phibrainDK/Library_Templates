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
#define INF (ll) 1e9
 
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
 
struct ST {
    ll n, ar[1 << 19], t[1 << 21], lazy[1 << 21];
    inline ll Op(ll a, ll b) { return min(a, b);}
    inline void updpro(ll laz, ll id, ll l, ll r) {
        if(laz) {
            t[id] += laz;
            lazy[id] += laz;
        }
    }
    inline void proh(ll id, ll l, ll r) {
        ll mid = (l + r) >> 1;
        updpro(lazy[id], id << 1, l, mid);
        updpro(lazy[id], id << 1 | 1, mid, r);
        lazy[id] = 0;
    }
    inline void Upd(ll x, ll y, ll val, ll id, ll l, ll r) {
        if(r <= x or y <= l) return;
        if(x <= l and r <= y) {
            updpro(val, id, l, r);
            return;
        }
        proh(id, l, r);
        ll mid = (l + r) >> 1;
        Upd(x, y, val, id << 1, l, mid);
        Upd(x, y, val, id << 1 | 1, mid, r);
        t[id] = Op(t[id << 1], t[id << 1 | 1]);
    }
    inline void Modify(ll p, ll val, ll id, ll l, ll r) {
        if(r <= p or p < l) return;
        if(l == p and l + 1 == r) { 
            t[id] = val; 
            lazy[id] = 0;
            return;
        }
        proh(id, l, r);
        ll mid = (l + r) >> 1;
        Modify(p, val, id << 1, l, mid);
        Modify(p, val, id << 1 | 1, mid, r);
        t[id] = Op(t[id << 1], t[id << 1 | 1]);
    }
    inline ii Que(ll x, ll y, ll id, ll l, ll r) {
        if(x >= r or y <= l) return {INF, INF};
        if(l + 1 == r) return t[id] == 0 ? make_pair(l, t[id]) : make_pair(INF, INF);
        if(x <= l and r <= y) {
            proh(id, l, r);
            if(t[id]) return {INF, INF};
            ll mid = (l + r) >> 1, L = t[id << 1], R = t[id << 1 | 1];
            if(R) return Que(x, y, id << 1, l, mid);
            return Que(x, y, id << 1 | 1, mid, r);
        }
        proh(id, l, r);
        ll mid = (l + r) >> 1;
        auto R = Que(x, y, id << 1 | 1, mid, r);
        if(R.ff == INF and R.ss == INF) return Que(x, y, id << 1, l, mid);
        return R;
    }
    inline void Build(ll id, ll l, ll r) {
        if(l + 1 == r) {
            t[id] = ar[l];
            return ;
        } 
        ll mid = (l + r) >> 1;
        Build(id << 1, l, mid);
        Build(id << 1 | 1, mid, r);
        t[id] = Op(t[id << 1], t[id << 1 | 1]);
    }
    inline void upd(ll x, ll y, ll val) { return Upd(x, y, val, 1, 0, n);}
    inline void modify(ll p, ll val) { Modify(p, val, 1, 0, n);}
    inline ii que(ll x, ll y) { return Que(x, y, 1, 0, n);}
    inline void build() { FER(i, 0, n << 2) lazy[i] = 0; return Build(1, 0, n);}
}st;
 
struct T {
    ll l, r, node, id, ta;
    bool is_cut, asc;
    T() {}
    T(ll l, ll r, ll node, ll id, ll ta, bool is_cut, bool asc) : l(l), r(r), node(node), id(id), ta(ta), is_cut(is_cut), asc(asc) {}
    inline T Op(T a, T b) {
        a.r = max(a.r, b.r);
        a.l = min(a.l, b.l);
        a.ta += b.ta;
        a.is_cut = false;
        return a;
    }
};
 
struct PQTree {
    ll n, boc;
    long long ans;
    vector<T> nodes, data;
    vector<vi> adj;
    inline void add(ll a, ll b) {
        adj[a].pb(b);
        adj[b].pb(a);
    }
    inline bool sonNode() {
        if(sz(nodes) <= 1) return false;
        auto top = nodes.back(); nodes.pop_back();
        auto bot = nodes.back(); nodes.pop_back();
        auto cur = top.Op(bot, top);
        if((bot.r - bot.l) and bot.is_cut == false and cur.r - cur.l + 1 - cur.ta == 0) {
            if(bot.asc and bot.r < top.l) { // ascending
            	adj.resize(boc + 1, vi());
                add(bot.node, top.node);
                bot = T(cur.l, cur.r, cur.node, bot.id, cur.ta, bot.is_cut, bot.asc);
                nodes.pb(bot);
                data[bot.node] = bot;
                return true;
            }
            else if(!bot.asc and bot.l > top.r) { // descending
                adj.resize(boc + 1, vi());
                add(bot.node, top.node);
                bot = T(cur.l, cur.r, cur.node, bot.id, cur.ta, bot.is_cut, bot.asc);
                nodes.pb(bot);
                data[bot.node] = bot;
                return true;
            }
            nodes.pb(bot), nodes.pb(top);
            return false;
        }
        nodes.pb(bot), nodes.pb(top);
        return false;
    }
    inline bool joinNode() {
        if(sz(nodes) <= 1) return false;
        auto top = nodes.back(); nodes.pop_back();
        auto bot = nodes.back(); nodes.pop_back();
        auto cur = top.Op(bot, top);
        if(cur.r - cur.l + 1 - cur.ta == 0) {
            adj.resize(boc + 1, vi());
            add(boc, bot.node);
            add(boc, top.node);
            cur.node = boc;
            cur.asc = bot.r < top.l ? true : false;
            data.pb(cur), nodes.pb(cur);
            boc ++;
            return true;
        }
        nodes.pb(bot), nodes.pb(top);
        return false;
    }
    inline bool cutNode(ll range) {
    	if(sz(nodes) <= 1) return false;
        auto top = nodes.back();
        auto [left_id, val_id] = st.que(0, top.id);
        if(!val_id) { // asumimos top nunca es especial node
            adj.resize(boc + 1, vi());
            T basic = T(-1 ,-1, -1, -1, 0, false, true);
            while(sz(nodes)) {
                top = nodes.back();
                add(boc, top.node);
                nodes.pop_back();
                basic = basic.id == -1? top : basic.Op(top, basic);
                if(left_id == top.id) break; // or basic.id
            }
            basic.node = boc;
            basic.is_cut = true;
            nodes.pb(basic);
            data.pb(basic);
            boc ++;
            return true;
        }
        return false;
    }
    inline void build(vi &ar) {
        n = sz(ar);
        st.n = n;
        ans = 0, boc = 0;
        FER(i, 0, n) st.ar[i] = INF; 
        st.build();
        vi mx = {-1}, mn = {-1};
        FER(i, 0, n) {
            st.modify(i, 1);
            while(sz(mx) > 1 and ar[mx.back()] < ar[i]) {
            	auto crt = mx.back(); mx.pop_back();
                st.upd(mx.back() + 1, crt + 1, ar[i] - ar[crt]);
            } 
            mx.pb(i);
            while(sz(mn) > 1 and ar[mn.back()] > ar[i]) {
            	auto crt = mn.back(); mn.pop_back();
                st.upd(mn.back() + 1, crt + 1, ar[crt] - ar[i]);
            }
            mn.pb(i);
            st.upd(0, i + 1, -1);
            T cur = T(ar[i], ar[i], boc, i, 1, false, true);
            data.pb(cur), nodes.pb(cur);
            boc ++;
            for( ; ; ) {
                if(sonNode()) continue;
                else {
                	if(joinNode()) continue;
                	else if (!cutNode(i)) break;
                }
            }
        }
    } 
    inline void dfs(ll u, ll pp) {
        auto comb = [&](ll x) {
            if(!x) return 0LL;
            return (1LL * x * (x + 1)) >> 1LL;
        };
        ll ch = 0;
        for(auto xd : adj[u]) if(xd != pp) {
            dfs(xd, u);
            ch ++;
        }
        if(!data[u].is_cut) ans += ch ? comb(ch) - 1LL : 0LL;
        else ans += ch;
    }
}pqTree;

int main() {
    // https://codeforces.com/contest/526/problem/F
    fastio;
    ll n, a, b; cin >> n;
    vi ar(n);
    FER(i, 0, n) {
    	cin >> a >> b; a --, b --;
    	ar[a] = b;
    }
    if(n == 1) return cout << "1\n", 0;
    pqTree.build(ar);
    assert (sz(pqTree.nodes) == 1);
    pqTree.dfs(pqTree.nodes.back().node, -1);
    cout << pqTree.ans + 1 << "\n";
    return 0;
}