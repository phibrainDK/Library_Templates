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

const int maxp = 1e6 + 1, maxv = 25, maxc = (int) 1e4 + 1;
int ptot, pr[maxp], d[maxp], cnt;
ll p[maxc];

inline ll mod_add(ll x, ll y, ll p) {
    return (x += y) < p ? x : x - p;
}
inline ll mod_mul(ll x, ll y, ll p) {
    ll ret = x * y - (ll)((long double)x * y / p + 0.5) * p;
    return ret < 0 ? ret + p : ret;
}
inline ll mod_pow(ll x, ll k, ll p) {
    ll ret = 1 % p;
    for( ; k > 0; k >>= 1, x = mod_mul(x, x, p))
    (k & 1) && (ret = mod_mul(ret, x, p));
    return ret;
}
inline bool miller_rabin(ll n) {
    if(n == 2) return 1;
    if(n < 2 || !(n & 1)) return 0;
    ll s = 0, r = n - 1;
    for( ; !(r & 1); r >>= 1, ++s);
    for(int i = 0; pr[i] < n && pr[i] < maxv; ++i) {
        ll cur = mod_pow(pr[i], r, n), nxt;
        for(int j = 0; j < s; ++j) {
            nxt = mod_mul(cur, cur, n);
            if(nxt == 1 && cur != 1 && cur != n - 1) return 0;
            cur = nxt;
        }
        if(cur != 1) return 0;
    }
    return 1;
}
inline void build(){
    FER(i, 2, maxp) {
        if(!d[i]) pr[ptot++] = d[i] = i;
        for(int j = 0, k; (k = i * pr[j]) < maxp; ++j) {
          d[k] = pr[j];
          if(d[i] == pr[j]) break;
        }
    }   
}

int main() {
    fastio;
    build();
    ll n; cin >> n;
    if(miller_rabin(n)) cout << "Yes\n" : cout << "No\n";
    return 0;
}