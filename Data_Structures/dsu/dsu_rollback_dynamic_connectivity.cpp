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
 
#define N 2900005
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
 
ll col[305][305], boc;
vi dy = {1, 0, -1, 0};
vi dx = {0, 1, 0, -1};
 
struct UFRB{
    ll comp, n;
    ll id[90005], tsz[90005];
    vi c;
    inline void build() { 
        comp = n;
        FER(i, 0, n) id[i] = i, tsz[i] = 1; 
        vi().swap(c);
    }
    inline ll find(ll x) { return x == id[x] ? x : find(id[x]);}
    inline bool unir(ll x, ll y) {
        ll p = x, q = y;
        if((x = find(x)) == (y = find(y))) return false;
        if(tsz[x] < tsz[y]) swap(x, y);
        tsz[x] += tsz[y];
        id[y] = x;
        c.pb(y);
        comp --;
        return true; 
    }
    inline ll token() { return sz(c);}
    inline void rollback(ll xt) {
        while(sz(c) > xt) {
            auto x = c.back(); c.pop_back();
            tsz[id[x]] -= tsz[x];
            id[x] = x;
            comp ++;
        }
    }
};
 
struct ST {
    ll n;
    UFRB uf;
    vector<vector<tuple<ll, ll>>> t;
    vii tnt;
    inline void build(ll m) { 
        uf.n = m;
        vii().swap(tnt);
        t.resize(n << 1);
        FER(i, 0, n << 1) vector<tuple<ll, ll>>().swap(t[i]);
        uf.build();
    }
    inline void modify(ll l, ll r, tuple<ll, ll> edge) {
        for(l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if(l & 1) t[l ++].pb(edge);
            if(r & 1) t[-- r].pb(edge);
        }
    }
    inline ll que(ll xd) {
        vi act, ans;
        vi().swap(act);
        for(xd += n; xd; xd >>= 1) act.pb(xd);
        reverse(all(act));
        ll lst = 0;
        FER(i, 0, min(sz(act), sz(tnt))) {
            auto [node, state] = tnt[i];
            if(node != act[i]) {
                lst = i;
                while(sz(tnt)) {
                    auto [x, y] = tnt.back();
                    uf.rollback(y);
                    tnt.pop_back();
                    vector<tuple<ll, ll>>().swap(t[x]);
                    if(x == node and state == y) break;
                }
                break;
            }
        }
        FER(i, lst, sz(act)) {
            tnt.pb({act[i], uf.token()});
            for(auto [a, b] : t[act[i]]) uf.unir(a, b);  
        }
        return uf.comp;
    }
}st;
 
int main() {
    fastio;
    // https://codeforces.com/contest/1303/problem/F
    // dsu + rollback for dynamic connectivity using segment tree 
    ll n, m, q, x, y, c; cin >> n >> m >> q;
    if(n == 1 and m == 1) {
        FER(i, 0, q) {
            cin >> x >> y >> c;
            cout << "1\n";
        }
        return 0;
    }
    map<ii, ii> Q;
    vector<tuple<ll, ll, ll, ll>> Ranges;
    auto rem = [&](ll a, ll b) {
        auto x = min(a, b);
        auto y = max(a, b);
        auto [l, r] = Q[{x, y}];
        Ranges.emplace_back(l, boc ++, x, y);
        Q.erase(make_pair(x, y));
    };
    auto add = [&](ll a, ll b) {
        auto x = min(a, b);
        auto y = max(a, b);
        Q[{x, y}] = {boc ++, INF};
    };
    auto explore = [&](ll i, ll j, ll color) {
        auto node = i * m + j;
        ll lts = col[i][j];
        if(color == lts) return;
        FER(tk, 0, 4) {
            auto a = i + dy[tk];
            auto b = j + dx[tk];
            if(a >= 0 and a < n and b >= 0 and b < m) {
                auto val = col[a][b];
                // antes conectados y ahora no conectados
                auto cur = a * m + b;
                if(col[a][b] == lts and col[a][b] != color) rem(cur, node);
                // no conectados y ahora conectados
                else if(col[a][b] != lts and col[a][b] == color) add(cur, node);
            }
        }
        col[i][j] = color;
    };
    vii tnt;
    FER(i, 0, n) FER(j, 0, m) {
        FER(tk, 0, 4) {
            auto a = i + dy[tk];
            auto b = j + dx[tk];
            auto node = i * m + j;
            if(a >= 0 and a < n and b >= 0 and b < m) {
                auto cur = a * m + b;
                auto A = min(cur, node);
                auto B = max(cur, node);
                tnt.pb({A, B});        
            }
        }
    }
    sort(all(tnt)); tnt.erase(unique(all(tnt)), tnt.end());
    for(auto [a, b] : tnt) add(a, b);
    vii().swap(tnt);
	vi Que;
    FER(i, 0, q) {
        cin >> x >> y >> c; x --, y --;
        explore(x, y, c);
        Que.pb(boc ++);
    }
    for(auto [aa, bb] : Q) {
        auto [x, y] = aa;
        auto [l, r] = bb;
        assert(r == INF);
        Ranges.emplace_back(l, boc, x, y);
    }
    sort(all(Ranges));
    st.n = boc;
    st.build(n * m);
    ll pq = 0;
    for(auto xd : Que) {
        while(pq < sz(Ranges) and get<0> (Ranges[pq]) <= xd) {
            auto [l, r, a, b] = Ranges[pq];
            st.modify(l, r, tuple<ll, ll>(a, b));
            pq ++;
        }
        cout << st.que(xd) << "\n";
    }
    return 0;
}