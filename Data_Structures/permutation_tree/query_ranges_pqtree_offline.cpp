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
    ll n, ar[1 << 19];
    T t[1 << 21];
    ii lazy[1 << 21];
    inline void updpro(ii laz, ll id, ll l, ll r) {
        if(laz.ff) {
            t[id].mn += laz.ff;
            lazy[id].ff += laz.ff;
        }
    }
    inline void updpush(ii laz, ll id, ll l, ll r) {
        if(laz.ss) {
            t[id].val += laz.ss * t[id].cnt;
            lazy[id].ss += laz.ss;
        }
    }
    inline void proh(ll id, ll l, ll r) {
        ll mid = (l + r) >> 1;
        updpro(lazy[id], id << 1, l, mid);
        updpro(lazy[id], id << 1 | 1, mid, r);
        if(t[id << 1].mn <= t[id << 1 | 1].mn) {
            updpush(lazy[id], id << 1, l, mid);
        }
        if(t[id << 1 | 1].mn <= t[id << 1].mn) {
            updpush(lazy[id], id << 1 | 1, mid, r);
        }
        lazy[id] = {0, 0};
    }
    inline void Upd(ll x, ll y, ii val, ll id, ll l, ll r) {
        if(r <= x or y <= l) return;
        if(x <= l and r <= y) {
            updpro(val, id, l, r);
            updpush(val, id, l, r);
            return;
        }
        proh(id, l, r);
        ll mid = (l + r) >> 1;
        Upd(x, y, val, id << 1, l, mid);
        Upd(x, y, val, id << 1 | 1, mid, r);
        auto nxt = t[id].val;
        t[id] = t[id].Op(t[id << 1], t[id << 1 | 1]);
        t[id].val = nxt;
    }
    inline void Modify(ll p, ll val, ll id, ll l, ll r) {
        if(r <= p or p < l) return;
        if(l == p and l + 1 == r) { 
            t[id] = T(val, 1, 0); 
            lazy[id] = {0, 0};
            return;
        }
        proh(id, l, r);
        ll mid = (l + r) >> 1;
        Modify(p, val, id << 1, l, mid);
        Modify(p, val, id << 1 | 1, mid, r);
        auto nxt = t[id].val;
        t[id] = t[id].Op(t[id << 1], t[id << 1 | 1]);
        t[id].val = nxt;
    }
    inline long long Query(ll x, ll y, ll id, ll l, ll r) {
        if(x >= r or y <= l) return 0LL;
        if(x <= l and r <= y) return t[id].val;
        proh(id, l, r);
        ll mid = (l + r) >> 1;
        long long L, R;
        L = Query(x, y, id << 1, l, mid);
        R = Query(x, y, id << 1 | 1, mid, r);
        return L + R;
    }
    inline void Build(ll id, ll l, ll r) {
        if(l + 1 == r) {
            t[id] = T(ar[l], 1, 0);
            return ;
        } 
        ll mid = (l + r) >> 1;
        Build(id << 1, l, mid);
        Build(id << 1 | 1, mid, r);
        t[id] = t[id].Op(t[id << 1], t[id << 1 | 1]);
    }
    inline void upd(ll x, ll y, ii val) { return Upd(x, y, val, 1, 0, n);}
    inline void modify(ll p, ll val) { Modify(p, val, 1, 0, n);}
    inline long long query(ll x, ll y) { return Query(x, y, 1, 0, n);}
    inline void build() { FER(i, 0, n << 2) lazy[i] = {0, 0}; return Build(1, 0, n);}
}st;

vii Q[1 << 19];
long long Answer[1 << 19];

struct PQTree {
    ll n;
    inline void build(vi &ar) {
        n = sz(ar);
        st.n = n;
        FER(i, 0, n) st.ar[i] = INF; 
        st.build();
        vi mx = {-1}, mn = {-1};
        FER(i, 0, n) {
            st.modify(i, 1);
            while(sz(mx) > 1 and ar[mx.back()] < ar[i]) {
            	auto crt = mx.back(); mx.pop_back();
                st.upd(mx.back() + 1, crt + 1, {ar[i] - ar[crt], 0});
            } 
            mx.pb(i);
            while(sz(mn) > 1 and ar[mn.back()] > ar[i]) {
            	auto crt = mn.back(); mn.pop_back();
                st.upd(mn.back() + 1, crt + 1, {ar[crt] - ar[i], 0});
            }
            mn.pb(i);
            st.upd(0, i + 1, {-1, 0});
            st.upd(0, n, {0, 1});
            for(auto [l, idx] : Q[i]) Answer[idx] = st.query(l, i + 1);
        }
    }
}pqTree;

int main() {
    // https://codeforces.com/contest/997/problem/E
    // counting good ranges on a given [l, r> offline (join nodes)
    fastio;
    ll n, q, l, r; cin >> n;
    vi ar(n);
    for(auto &xd : ar) cin >> xd;
    cin >> q;
    FER(i, 0, q) {
        cin >> l >> r; l --, r --;
        Q[r].pb({l, i});
    }
    pqTree.build(ar);
    FER(i, 0, q) cout << Answer[i] << "\n";
    return 0;
}