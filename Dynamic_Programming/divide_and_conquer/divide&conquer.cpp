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
#define INF (ll) 2e15
 
using namespace std;
using namespace __gnu_pbds;
 
 
typedef long long ll;
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

int main() {
    fastio;
    // https://codeforces.com/contest/868/problem/F
    // opt(i, j) <= opt(i, j + k), k > 0
    ll n, k, ans = 0; cin >> n >> k;
    vi ar(n + 1);
    FER(i, 1, n + 1) cin >> ar[i];
    vi dp(n + 1, 0), frec(n + 1, 0), vec(n + 1, 0);
    ll L = 1, R = 0, resp = 0;
    auto Add = [&](ll p) { resp += frec[ar[p]] ++;};
    auto Rem = [&](ll p) { resp -= -- frec[ar[p]];};
    auto Q = [&](ll l, ll r) {
        if(l > r) return 0LL;
        while(L < l) Rem(L ++);
        while(L > l) Add(-- L);
        while(R < r) Add(++ R);
        while(R > r) Rem(R --);
        return resp;
    };
    function<void(ll, ll, ll, ll)> dc = [&](ll l, ll r, ll optL, ll optR) {
        if(l > r) return;
        ll mid = (l + r) >> 1, RT = min(mid, optR);
        ii best = {vec[RT] + Q(RT + 1, mid), RT};
        IFR(i, RT - 1, optL) best = min(best, {vec[i] + Q(i + 1, mid), i});
        dp[mid] = best.ff;
        dc(l, mid - 1, optL, best.ss);
        dc(mid + 1, r, best.ss, optR);
    };
    FER(i, 1, n + 1) {
        ans += frec[ar[i]] ++;
        vec[i] = ans;
    }
    FER(i, 1, n + 1) frec[ar[i]] = 0;
    FER(i, 1, k) dc(1, n, 1, n), vec = dp;
    auto CB = dp[n];
    cout << CB << "\n";
    return 0;
}