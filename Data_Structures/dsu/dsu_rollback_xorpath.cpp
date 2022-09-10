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

struct LST {
    ll n;
    vi L, R, T, ar;
    inline ll Op(ll a, ll b) { return a + b;}
    inline ll newP(ll l, ll r) {
        L.pb(l), R.pb(r), T.pb(Op(T[l], T[r]));
        return sz(T) - 1;
    }
    inline ll newL(ll val) {
        L.pb(0), R.pb(0), T.pb(val);
        return sz(T) - 1;
    }
    inline ll Upd(ll p, ll val, ll id, ll l, ll r) {
        if(l + 1 == r) return newL(val);
        ll mid = (l + r) >> 1;
        if(p < mid) return newP(Upd(p, val, L[id], l, mid), R[id]);
        return newP(L[id], Upd(p, val, R[id], mid, r));
    }
    inline ll Que(ll x, ll y, ll id, ll l, ll r) {
        if(x >= r or y <= l) return 0;
        if(x <= l and r <= y) return T[id];
        ll mid = (l + r) >> 1;
        auto zL = Que(x, y, L[id], l, mid);
        auto zR = Que(x, y, R[id], mid, r);
        return Op(zL, zR);
    }
    inline ll Build(ll l, ll r) {
        if(l + 1 == r) return newL(ar[l]);
        ll mid = (l + r) >> 1;
        auto L = Build(l, mid);
        auto R = Build(mid, r);
        return newP(L, R);
    }
    inline ll upd(ll p, ll val, ll x) { return Upd(p, val, x, 0, n);}
    inline ll que(ll x, ll y, ll t) { return Que(x, y, t, 0, n);}
    inline ll build() { return Build(0, n);}
};

ll rt[1 << 20];

struct UFRB{
    ll n, boc;
    map<ll, ll> id, tsz, d;
    vi peso;
    vii c, jenna;
    inline void add(ll x, ll y){
        for(auto [xd, xe]: jenna) x = min(x ^ xd, x);
        if(x) jenna.pb({x, y});
    }
    inline void build() { boc = 0; vii().swap(c);}
    inline ll find(ll x) { return x == id[x] ? x : find(id[x]);}
    inline ll dist(ll x) {
        ll ans = 0;
        while(x != id[x]) ans ^= d[x], x = id[x];
        return ans;
    }
    inline bool unir(ll x, ll y, ll z) {
        if(!id.count(x)) id[x] = x, tsz[x] = 1, d[x] = 0;
        if(!id.count(y)) id[y] = y, tsz[y] = 1, d[y] = 0;
        ll p = x, q = y;
        if((x = find(x)) == (y = find(y))) {
            auto Z = dist(p) ^ dist(q);
            add(Z ^ z, ++ boc);
            peso.pb(Z ^ z);
            return false;
        }
        if(tsz[x] < tsz[y]) swap(x, y);
        tsz[x] += tsz[y];
        id[y] = x;
        z ^= (dist(p) ^ dist(q));
        c.pb({y, d[y]});
        d[y] = z;
        add(0, boc ++);
        peso.pb(0);
        return true; 
    }
    inline ii token() { return {sz(c), sz(peso)};}
    inline void rollback(ll xt, ll y) {
        while(sz(c) > xt) {
            auto [x, w] = c.back(); c.pop_back();
            tsz[id[x]] -= tsz[x];
            id[x] = x;
            d[id[x]] = w;
        }
        while(sz(peso) > y) {
            if(sz(jenna) and jenna.back().ss > y) jenna.pop_back();
            auto tp = peso.back(); peso.pop_back();
            boc --;
        }
    }
};

struct ST {
    ll n, CB[1 << 19];
    UFRB uf;
    vector<tuple<ll, ll, ll>> t[1 << 20];
    ii Q[1 << 19];
    inline void build() { 
        uf.build(); 
        FER(i, 0, n) Q[i] = {-1, -1}, CB[i] = -1;
        FER(i, 0, n << 2) t[i].clear();
    }
    inline void Upd(ll x, ll y, tuple<ll, ll, ll> edge, ll id, ll l, ll r) {
        if(r <= x or y <= l) return;
        if(x <= l and r <= y) {
            t[id].pb(edge);
            return;
        }
        ll mid = (l + r) >> 1;
        Upd(x, y, edge, id << 1, l, mid);
        Upd(x, y, edge, id << 1 | 1, mid, r);
    }
    inline void modify(ll l, ll r, tuple<ll, ll, ll> edge) { Upd(l, r, edge, 1, 0, n);}
    inline void dfs(ll id, ll l, ll r) {
        auto [xA, yB] = uf.token();
        for(auto [a, b, c] : t[id]) uf.unir(a, b, c);
        if(l + 1 == r) {
            auto [x, y] = Q[l];
            if(x != -1 and y != -1) {
                auto a = uf.dist(x);
                auto b = uf.dist(y);
                vii vec;
                for(auto xd : uf.jenna) vec.pb(xd);
                sort(all(vec));
                ll ans = a ^ b;
                IFR(i, sz(vec) - 1, 0) ans = min(ans, ans ^ vec[i].ff);
                CB[l] = ans;
            }
        }
        else{
	        ll mid = (l + r) >> 1;
	        dfs(id << 1, l, mid);
	        dfs(id << 1 | 1, mid, r);
        }
        uf.rollback(xA, yB);
    }
}st;


int main() {
    // https://codeforces.com/contest/938/problem/G
    // rollback + dynamic connectivity
    fastio;
    ll n, m, x, y, d; cin >> n >> m;
    map<ii, tri> mt;
    vector<tuple<ll, ll, ll>> edges;
    FER(i, 0, m) {
        cin >> x >> y >> d; x --, y --;
        auto a = min(x, y);
        auto b = max(x, y);
        edges.emplace_back(d, a, b);
        mt[{a, b}] = {0, {INF, d}};
    }
    ll q, ty; cin >> q;
    vii Q;
    st.n = q + 1;
    st.build();
    FER(i, 0, q) {
        cin >> ty;
        if(ty == 1) {
            cin >> x >> y >> d; x --, y --;
            auto a = min(x, y);
            auto b = max(x, y);
            mt[{a, b}] = {i + 1, {INF, d}};
        }
        else if(ty == 2) {
            cin >> x >> y; x --, y --;
            auto a = min(x, y);
            auto b = max(x, y);
            auto [_x, _y] = mt[{a, b}];
            auto [_z, _w] = _y;
            mt[{a, b}] = {_x, {i + 1, _w}};
        }
        else {
            cin >> x >> y; x --, y --;
            st.Q[i + 1] = {x, y};
        }
    }
    for(auto &[a, b] : mt) {
        auto &[c, d] = b;
        auto &[e, f] = d;
        if(e == INF) e = q + 1;
    }
    for(auto [a, b] : mt) {
        auto [c, d] = b;
        auto [e, f] = d;
        st.modify(c, e, {a.ff, a.ss, f});
    }
    st.dfs(1, 0, st.n);
    FER(i, 0, st.n) if(st.CB[i] != -1) cout << st.CB[i] << "\n"; 
    return 0;
}