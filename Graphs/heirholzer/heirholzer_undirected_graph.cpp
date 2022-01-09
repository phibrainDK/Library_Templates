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


typedef long long  ll;
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

vi graph[1 << 16];

int main() {
    // https://codeforces.com/contest/1494/problem/F
    fastio;
    ll n, m; cin >> n >> m;
    vii edges;
    vi gra(n, 0);
    FER(i, 0, m) {
        ll a, b; cin >> a >> b; a --, b --;
        edges.pb({a, b});
        graph[a].pb(b);
        graph[b].pb(a);
        gra[a] ++, gra[b] ++;
    }
    vector<set<ll>> adj(n), other(n);
    vi tnt, vis;
    function<void(ll u)>  Heirholzer = [&](ll u) {
        while(sz(adj[u])) {
            auto it = adj[u].end();
            it --;
            adj[u].erase(*it);
            adj[*it].erase(u);
            Heirholzer(*it);
        }
        tnt.pb(u);
    };
    auto check = [&](ll u) {
        vi().swap(tnt);
        vi cnt(n, 0);
        FER(i, 0, n) cnt[i] = sz(adj[i]);
        Heirholzer(u);
        FER(i, 0, n) if(sz(adj[i])) return 0;
        FER(i, 0, sz(tnt) - 1) {
        	auto x = tnt[i];
        	auto y = tnt[i + 1];
        	cnt[x] --, cnt[y] --;
        }
        FER(i, 0, n) if(cnt[i] != 0) return 0;
        return 1;
    };
    FER(i, 0, n) {
        vector<set<ll>>().swap(adj);
        vector<set<ll>>().swap(other);
        adj.resize(n);
        other.resize(n);
        for(auto [a, b] : edges) adj[a].insert(b), adj[b].insert(a), other[a].insert(b), other[b].insert(a);
        vi cur;
        for(auto xd : graph[i]) {
            if(gra[xd] & 1) {
                adj[xd].erase(i);
                adj[i].erase(xd);
                other[xd].erase(i);
                other[i].erase(xd);
                cur.pb(xd);
            }
        }
        if(check(i)) {
        	FER(j, 0, sz(tnt) - 1) {
        		auto x = tnt[j];
        		auto y = tnt[j + 1];
        		if(!other[x].count(y)) goto next;
        	}
            if(sz(cur)) {
                tnt.pb(-2);
                for(auto xd : cur) {
                    tnt.pb(xd);
                    tnt.pb(i);
                }
            }
            cout << sz(tnt) << "\n";
            for(auto xd : tnt) cout << xd + 1 << " "; cout << "\n";
            return 0;
        }
        next:
        	continue;
    }
    FER(i, 0, n) {
        vector<set<ll>>().swap(adj);
        vector<set<ll>>().swap(other);
        adj.resize(n);
        other.resize(n);
        for(auto [a, b] : edges) adj[a].insert(b), adj[b].insert(a), other[a].insert(b), other[b].insert(a);
        vi cur;
        for(auto xd : graph[i]) if(gra[xd] & 1){
            adj[xd].erase(i);
            adj[i].erase(xd);
            other[xd].erase(i);
            other[i].erase(xd);
            cur.pb(xd);
        }
        vector<set<ll>> keep = adj;
        for(auto xd : graph[i]) {
            if(gra[xd] & 1) {
                adj = keep;
                other = keep;
                adj[xd].insert(i), adj[i].insert(xd);
                other[xd].insert(i), other[i].insert(xd);
                if(check(xd)) {
                    FER(j, 0, sz(tnt) - 1) {
                    auto x = tnt[j];
                    auto y = tnt[j + 1];
                    if(!other[x].count(y)) goto nexto;
                }
                reverse(all(tnt));
                if(tnt.back() != i) goto nexto;
                if(sz(cur) > 1) {
                    tnt.pb(-2);
                    for(auto gg : cur) {
                        if(xd == gg) continue;
                        tnt.pb(gg);
                        tnt.pb(i);
                    }
                }
                cout << sz(tnt) << "\n";
                for(auto gg : tnt) cout << gg + 1 << " "; cout << "\n";
                return 0;
                }
            }
            nexto:
                continue;
        }
    }
    cout << "0\n";
    return 0;
}