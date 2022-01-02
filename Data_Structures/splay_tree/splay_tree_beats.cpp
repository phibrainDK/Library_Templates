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

struct T{
    ll val, ta, sum, fmx, smx, cmx;
    bool t;
    T(){}
    T(ll val, ll ta, ll sum, bool t, ll fmx, ll smx, ll cmx) : 
        val(val), ta(ta), sum(sum), t(t), fmx(fmx), smx(smx), cmx(cmx){}
    inline T Op(T a, T b){
        if(a.fmx < b.fmx){
            a.cmx = 0;
            a.smx = a.fmx;
            a.fmx = b.fmx;
        }
        if(a.fmx == b.fmx){
            a.cmx += b.cmx;
            a.smx = max(a.smx, b.smx);
        }
        else a.smx = max(a.smx, b.fmx);
        a.sum += b.sum;
        return a;
    }
    inline void Umin(ll x){
        sum += (x - fmx) * cmx;
        val = min(val, x);
        fmx = x;
    }
}; 
 
struct STB{
    T nil;
    vector<T> tree;
    vi L, R, P, ar;
    ll n, root;
    inline void preprocess(){
        nil = T(0, 0, 0, false, -INF, -INF, 0);
        tree.pb(nil);
        L.pb(0);
        R.pb(0);
        P.pb(0);
    }
    inline void updpro(T val, ll id){
        if(val.fmx < tree[id].fmx){
            tree[id].Umin(val.fmx);
        }
    }
    inline void proh(ll id){
        if(L[id]) updpro(tree[id], L[id]);
        if(R[id]) updpro(tree[id], R[id]);
    }
    inline void upd(ll x){
        ll idl = L[x], idr = R[x];
        tree[x].ta = tree[idl].ta + tree[idr].ta + 1;
        T cur = nil;
        cur.fmx = tree[x].val;
        cur.smx = -INF;
        cur.cmx = 1;
        cur.sum = tree[x].val;
        if(R[x]) cur = cur.Op(cur, tree[R[x]]);
        if(L[x]) cur = cur.Op(tree[L[x]], cur);
        tree[x].fmx = cur.fmx;
        tree[x].smx = cur.smx;
        tree[x].cmx = cur.cmx;
        tree[x].sum = cur.sum; 
    }
    inline void push(ll id){
        if(id == 0) return;
        proh(id);
        if(tree[id].t){
            swap(L[id], R[id]);
            tree[L[id]].t = !tree[L[id]].t;
            tree[R[id]].t = !tree[R[id]].t;
            tree[id].t = false;
        }
    }
    inline void set(ll idx, ll idy, ll d){
        if(!idx) {
            P[idy] = idx;
            return;
        }
        if(d == 0){
            L[idx] = idy;
            if(idy) P[idy] = idx;
        }
        else{
            R[idx] = idy;
            if(idy) P[idy] = idx;
        }
    }
    inline ll get(ll idx, ll idy) { return L[idx] == idy? 0 : 1;}
    inline void rot(ll x, ll d){
        if(d == 0){
            ll y = L[x], z = P[x];
            set(x, R[y], d);
            set(y, x, 1);
            set(z, y, get(z, x));
            upd(x), upd(y);
        }
        else{
            ll y = R[x], z = P[x];
            set(x, L[y], d);
            set(y, x, 0);
            set(z, y, get(z, x));
            upd(x), upd(y);
        }
    }
    inline void splay(ll x){
        push(x);
        while(P[x]){
            ll y = P[x], z = P[y];
            ll dy = get(y, x), dz = get(z, y);
            if(!z) rot(y, dy);
            else if(dy == dz) rot(z, dz), rot(y, dy);
            else rot(y, dy), rot(z, dz);
        }
        upd(x);
    }
    inline ll getnode(ll x, ll pos){
        while(push(x), tree[L[x]].ta != pos){
            pos < tree[L[x]].ta? x = L[x] : (pos -= tree[L[x]].ta + 1, x = R[x]);
        }
        return splay(x), x;
    }
    inline ii split(ll x, ll l){
        ll t1, t2;
        if(!l) return ii{0, x};
        else{
            t1 = getnode(x, l - 1);
            t2 = R[t1];
            R[t1] = 0;
            P[t1] = 0;
            P[t2] = 0;
            upd(t1);
            return ii{t1, t2};
        }
    }
    inline ll unir(ll x, ll y){
        if(!y) return x;
        if(!x)  return y;
        x = getnode(x, tree[x].ta - 1);
        set(x, y, 1);
        upd(x);
        return x;
    }
    inline void UpdMinimo(ll id, ll val){
        if(tree[id].fmx <= val) return;
        if(tree[id].smx < val and tree[id].fmx > val){
            tree[id].Umin(val);
            return;
        }
        tree[id].val = min(tree[id].val, val);
        proh(id);
        if(L[id]) UpdMinimo(L[id], val);
        if(R[id]) UpdMinimo(R[id], val);
        upd(id);
        return;
    }
    inline void UpdMin(ll l, ll r, ll val){
        ll t1, t2, t3;
        auto ret = split(root, r);
        auto ket = split(ret.ff, l);
        t1 = ket.ff, t2 = ket.ss, t3 = ret.ss;
        UpdMinimo(t2, val);
        root = unir(t1, unir(t2, t3));
    }
    inline ll que(ll l, ll r){
        ll t1, t2, t3;
        auto ret = split(root, r);
        auto ket = split(ret.ff, l);
        t1 = ket.ff, t2 = ket.ss, t3 = ret.ss;
        ll ans = tree[t2].sum;
        root = unir(unir(t1, t2), t3);
        return ans;
    }
    inline void Delete(ll l, ll r){
        ll t1, t2, t3;
        auto ret = split(root, r);
        auto ket = split(ret.ff, l);
        t1 = ket.ff, t2 = ket.ss, t3 = ret.ss;
        root = unir(t1, t3);
    }
    inline void Insert(ll p, ll val){
        T cur = nil;
        cur = T(val, 1, val, false, val, -INF, 1);
        tree.pb(cur);
        R.pb(0);
        L.pb(0);
        P.pb(0);
        ll cur_id = sz(tree) - 1;
        ll m = tree[root].ta;
        if(m == p){
            root = unir(root, cur_id);
            return;
        }
        if(p == 0){
            root = unir(cur_id, root);
            return;
        }
        ll t1, t2;
        auto ret = split(root, p);
        t1 = ret.ff, t2 = ret.ss;
        root = unir(t1, unir(cur_id, t2));
    }
    inline ll Build(ll l, ll r){
        if(l == r) return 0;
        ll mid = (l + r)>>1;
        T x;
        x = T(ar[mid], 1, ar[mid], false, ar[mid], -INF, 1);
        tree.pb(x);
        L.pb(0);
        R.pb(0);
        P.pb(0);
        ll cur_id = sz(tree) - 1;
        set(cur_id, Build(l, mid), 0);
        set(cur_id, Build(mid + 1, r), 1);
        upd(cur_id);
        return cur_id;
    }
    inline void build(){
        root = Build(0, n);
    }
}st;

int main() {
    fastio;
    ll n, q; cin >> n >> q;
    st.n = n;
    FER(i, 0, n) cin >> st.ar[i];
    st.preprocess();
    st.build();
    FER(i, 0, q) {
        // answer queries
    }   
    return 0;
}