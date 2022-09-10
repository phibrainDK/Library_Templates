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
struct T {
    ll mn, cnt;
    long long val;
    T() {}
    T(ll mn, ll cnt, long long val) : mn(mn), cnt(cnt), val(val) {}
    inline T Op(T a, T b) {
        if(a.mn != b.mn) {
            auto cur = a.mn < b.mn ? T(a.mn, a.cnt, a.val) : T(b.mn, b.cnt, b.val);
            return cur;
        }
        auto cur = T(a.mn, a.cnt + b.cnt, a.val + b.val);
        return cur;
    }
};

struct ST {
    vi ar, L, R;
    vector<tri> lazy;
    T wk;
    vector<T> t;
    ll n;
    inline ll newLazy(ll id, ll l, ll r) {
        L.pb(L[id]), R.pb(R[id]), lazy.pb(lazy[id]), t.pb(t[id]);
        lazy[sz(t) - 1].tm3 = 1;
        return sz(t) - 1;
    }
    inline ll newLeaf(T val) {
        L.pb(0), R.pb(0), t.pb(val), lazy.pb({0, {0, 0}});
        return sz(t) - 1;
    }
    inline ll newP(ll l, ll r, ll val) {
        L.pb(l), R.pb(r), lazy.pb({0, {0, 0}});
        auto cur = wk.Op(t[l], t[r]);
        cur.val = val;
        t.pb(cur);
        return sz(t) - 1;
    }
    inline void updpro(tri laz, ll id, ll l, ll r) {
        if(laz.tm1) {
            t[id].mn += laz.tm1;
            lazy[id].tm1 += laz.tm1;
        }
    }
    inline void updpush(tri laz, ll id, ll l, ll r) {
        if(laz.tm2) {
            t[id].val += laz.tm2 * t[id].cnt;
            lazy[id].tm2 += laz.tm2;
        }
    }
    inline void proh(ll id, ll l, ll r) {
        ll mid = (l + r) >> 1;
        if(lazy[id].tm3) {
            if(l >= r) return;
            auto Lx = newLazy(L[id], l, mid);
            auto Ry = newLazy(R[id], mid, r);
            updpro(lazy[id], Lx, l, mid);
            updpro(lazy[id], Ry, mid, r);
            if(t[Lx].mn <= t[Ry].mn) updpush(lazy[id], Lx, l, mid);
            if(t[Ry].mn <= t[Lx].mn) updpush(lazy[id], Ry, mid, r);
            L[id] = Lx;
            R[id] = Ry;
            lazy[id] = {0, {0, 0}};
            return;
        }
    }
    inline ll Upd(ll x, ll y, ii val, ll id, ll l, ll r) {
        if(r <= x or y <= l) return id;
        if(x <= l and r <= y) {
            auto node = newLazy(id, l, r);
            updpro({val.ff, {val.ss, 0}}, node, l, r);
            updpush({val.ff, {val.ss, 0}}, node, l, r);
            return node;
        }
        proh(id, l, r);
        ll mid = (l + r) >> 1, left, right;
        left = Upd(x, y, val, L[id], l, mid);
        right = Upd(x, y, val, R[id], mid, r);
        return newP(left, right, t[id].val);
    }
    inline ll Modify(ll p, ll val, ll id, ll l, ll r) {
        if(r <= p or p < l) return id;
        if(l == p and l + 1 == r) return newLeaf(T(val, 1, 0));
        proh(id, l, r);
        ll mid = (l + r) >> 1, left, right;
        left = Modify(p, val, L[id], l, mid);
        right = Modify(p, val, R[id], mid, r);
        return newP(left, right, t[id].val);
    }
    inline long long Query(ll x, ll y, ll id, ll l, ll r) {
        if(x >= r or y <= l) return 0LL;
        if(x <= l and r <= y) return t[id].val;
        proh(id, l, r);
        ll mid = (l + r) >> 1;
        long long Left, Right;
        Left = Query(x, y, L[id], l, mid);
        Right = Query(x, y, R[id], mid, r);
        return Left + Right;
    }
    inline ll Build(ll l, ll r) {
        if(l + 1 == r) return newLeaf(T(ar[l], 1, 0));
        ll mid = (l + r) >> 1, left, right;
        left = Build(l, mid);
        right = Build(mid, r);
        return newP(left, right, 0);
    }
    inline ll upd(ll x, ll y, ii val, ll idx) { return Upd(x, y, val, idx, 0, n);}
    inline ll modify(ll p, ll val, ll idx) { return Modify(p, val, idx, 0, n);}
    inline long long query(ll x, ll y, ll idx) { return Query(x, y, idx, 0, n);}
    inline ll build() { return Build(0, n);}
}st;

struct PQTree {
    ll n, rt[1 << 18], boc;
    inline void build(vi &ar) {
        n = sz(ar), boc = 0;
        st.n = n;
        FER(i, 0, n) st.ar.pb(INF); 
        rt[0] = st.build();
        vi mx = {-1}, mn = {-1};
        FER(i, 0, n) {
            auto root = rt[i];
            root = st.modify(i, 1, root);
            while(sz(mx) > 1 and ar[mx.back()] < ar[i]) {
            	auto crt = mx.back(); mx.pop_back();
                root = st.upd(mx.back() + 1, crt + 1, {ar[i] - ar[crt], 0}, root);
            } 
            mx.pb(i);
            while(sz(mn) > 1 and ar[mn.back()] > ar[i]) {
            	auto crt = mn.back(); mn.pop_back();
                root = st.upd(mn.back() + 1, crt + 1, {ar[crt] - ar[i], 0}, root);
            }
            mn.pb(i);
            root = st.upd(0, i + 1, {-1, 0}, root);
            rt[i + 1] = st.upd(0, n, {0, 1}, root);
        }
    }
}pqTree;

int main() {
    // https://codeforces.com/contest/997/problem/E
    // counting good ranges on a given [l, r> onnline (join nodes)
    fastio;
    ll n, q, l, r; cin >> n;
    vi ar(n);
    for(auto &xd : ar) cin >> xd;
    pqTree.build(ar);
    cin >> q;
    FER(i, 0, q) {
        cin >> l >> r; l --, r --;
        auto valor = st.query(l, r + 1, pqTree.rt[r + 1]);
        cout << valor << "\n";
    }
     return 0;
}