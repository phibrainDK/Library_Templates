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

#include <complex>
namespace FFT{
    // blog.myungwoo.kr/54
    typedef complex<double> base;
    // typedef long long ll;
 
    // #define all(x) (x).begin(), (x).end()
    // #define sz(x) ((int)(x).size())
 
    const double C_PI = acos(-1);
 
    inline void fft(vector <base> &a, bool invert){
        int n = sz(a);
        for(int i = 0, j = 0; i < n; ++ i) {
            if(i > j) swap(a[i], a[j]);
            for(int k = n >> 1; (j ^= k) < k; k >>= 1);
        }
        for (int len = 2; len <= n; len <<= 1){
            double ang = 2 * C_PI / len * (invert ? -1 : 1);
            base wlen(cos(ang), sin(ang));
            for (int i = 0; i < n; i += len){
                base w(1);
                for (int j = 0; j < len/2; j ++){
                    if((j & 511) == 511) w = base(cos(ang * j), sin(ang * j));
                    base u = a[i + j], v = a[i + j + len / 2] * w;
                    a[i + j] = u + v;
                    a[i + j + len / 2] = u - v;
                    w *= wlen;
                }
            }
        }
        if (invert){
            for (int i = 0; i < n; i ++) a[i] /= n;
        }
    }
 
    inline void multiply(const vector<ll> &a,const vector<ll> &b,vector<ll> &res, const int MOD){
        vector <base> fa(all(a)), fb(all(b));
        int n = 1;
        while (n < max(sz(a), sz(b))) n <<= 1; n <<= 1;
        fa.resize(n); fb.resize(n);
        fft(fa,false); fft(fb,false);
        for (int i = 0; i < n; i ++) fa[i] *= fb[i];
        fft(fa,true);
        res.resize(n);
        for (int i = 0;i < n; i ++) res[i] = ((ll)(fa[i].real() + (fa[i].real() > 0 ? 0.5 : -0.5))) % MOD;
    }
 
    inline void multiply_with_modulo(const vector<ll> &a, const vector<ll> &b, vector<ll> &res, const ll MOD){
        int n = 1;
        while (n < max(sz(a), sz(b))) n <<= 1; n <<= 1;
        vector <base> A(n), B(n);
        int L_BLOCK = 10;   //2^L_BLOCK ~= sqrt(MOD).
        for(int i = 0; i < n; i ++) A[i] = (i < sz(a) ? base(a[i] & ((1 << L_BLOCK) - 1), a[i] >> L_BLOCK) : base(0));
        for(int i = 0; i < n; i ++) B[i] = (i < sz(b) ? base(b[i] & ((1 << L_BLOCK) - 1), b[i] >> L_BLOCK) : base(0));
        fft(A, false); fft(B, false);
        vector <base> f1(n), f2(n), f3(n), f4(n);
        for(int i = 0; i < n; i ++) {
            int j = (n - i) & (n - 1);
            f2[i] = (A[i] + conj(A[j])) * base(0.5, 0);
            f1[i] = (A[i] - conj(A[j])) * base(0, -0.5);
            f4[i] = (B[i] + conj(B[j])) * base(0.5, 0);
            f3[i] = (B[i] - conj(B[j])) * base(0, -0.5);
        }
        for(int i = 0; i < n; i ++) {
            A[i] = f1[i] * f3[i] + f1[i] * f4[i] * base(0, 1);
            B[i] = f2[i] * f4[i] * base(0, 1) + f2[i] * f3[i];
        }
        fft(A, true); fft(B, true);
        res.resize(n);
        for(int i = 0; i < n; i ++) {
            long long g1=(ll)(A[i].real() + 0.5) % MOD;  //A[i].real > 0 
            long long g2=(ll)(A[i].imag() + 0.5) % MOD;
            long long g3=(ll)(B[i].real() + 0.5) % MOD;
            long long g4=(ll)(B[i].imag() + 0.5) % MOD;
            res[i] = (g4 + ((g2 + g3) << L_BLOCK) + (g1 << (L_BLOCK << 1))) % MOD;
        }
    }
    
    inline void multiply_big(vector<ll> &a, vector<ll> &b, vector <ll> &res){
        int n = 1;
        while (n < max(sz(a), sz(b))) n <<= 1; n <<= 1;
        vector <base> A(n), B(n);
        int L_BLOCK = 10;
        for(int i = 0; i < n; i++) A[i] = (i < sz(a) ? base(a[i] & ((1 << L_BLOCK) - 1), a[i] >> L_BLOCK) : base(0));
        for(int i = 0; i < n; i++) B[i] = (i < sz(b) ? base(b[i] & ((1 << L_BLOCK) - 1), b[i] >> L_BLOCK) : base(0));
        fft(A, false); fft(B, false);
        vector <base> f1(n), f2(n), f3(n), f4(n);
        for(int i = 0; i < n; i ++) {
            int j = (n - i) & (n - 1);
            f2[i] = (A[i] + conj(A[j])) * base(0.5, 0);
            f1[i] = (A[i] - conj(A[j])) * base(0, -0.5);
            f4[i] = (B[i] + conj(B[j])) * base(0.5, 0);
            f3[i] = (B[i] - conj(B[j])) * base(0, -0.5);
        }
        for(int i = 0; i < n; i ++) {
            A[i] = f1[i] * f3[i] + f1[i] * f4[i] * base(0, 1);
            B[i] = f2[i] * f4[i] * base(0, 1) + f2[i] * f3[i];
        }
        fft(A, true); fft(B, true);
        res.resize(n);
        for(int i = 0; i < n; i ++) {
            ll g1 = (ll)(A[i].real() + 0.5);
            ll g2 = (ll)(A[i].imag() + 0.5);
            ll g3 = (ll)(B[i].real() + 0.5);
            ll g4 = (ll)(B[i].imag() + 0.5);
            res[i] = (g4 + ((g2 + g3) << (L_BLOCK)) + (g1 << (L_BLOCK << 1)));
        }
    }
}

ll MOD;

inline bool is_zero(vi x) { return x.empty();}
inline vi operator * (vi a, vi b) {
    if(is_zero(a) or is_zero(b)) return {};
    vi A, B, C;
    for(auto xd : a) A.pb(xd);
    for(auto xd : b) B.pb(xd);
    FFT::multiply_with_modulo(A, B, C, MOD);
    while(sz(C) and !C.back()) C.pop_back();
    return C;
}
inline vi operator - (vi a, vi b) {
    ll n = max(sz(a), sz(b));
    vi ans(n);
    a.resize(n, 0);
    b.resize(n, 0);
    FER(i, 0, n) ans[i] = add(a[i], b[i], MOD);
    while(sz(ans) and !ans.back()) ans.pop_back();
    return ans;
}
inline vi operator * (const vi a, const ll &x) {
    ll n =sz(a);
    vi ans(n);
    FER(i, 0, n) ans[i] = mul(ans[i], x, MOD);
    return ans;
}

inline vi mod_xk(vi a, ll k) { return {a.begin(), a.begin() + min(k, sz(a))};}
inline vi mulx(vi a, ll x) {
    ll cur = 1;
    vi ans(a);
    FER(i, 0, sz(a)) ans[i] = mul(ans[i], cur, MOD), cur = mul(cur, x, MOD);
    return ans;
}
inline vi mul_sq(vi a, ll x) {
    ll cur = x, total = 1, xx = mul(x, x, MOD);
    vi ans(a);
    FER(i, 0, sz(a)) ans[i] = mul(ans[i], total, MOD), total = mul(total, cur, MOD), cur = mul(cur, xx, MOD);
    return ans;
}
inline vi substr(vi a, ll l, ll r) {
    l = min(l, sz(a));
    r = min(r, sz(a));
    return vi(a.begin() + l, a.begin() + r);
}
inline vi reverse_it(vi a, ll n, bool rev = 0) {
    vi ans(a);
    if(rev) ans.resize(max(n, sz(ans)));
    reverse(all(ans));
    return mod_xk(ans, n);
}
inline vi inverse(vi a, int n) {
    assert(!is_zero(a));
    assert(a[0] != 0);
    vi ans = {bp(a[0], MOD - 2, MOD)};
    for(int i = 1; i < n; i *= 2) {
        ans = mod_xk(ans * 2 - ans * ans * mod_xk(a, i << 1), i << 1);
    }
    return mod_xk(ans, n);
}
inline pair<vi, vi> divmod_slow(vi a, vi b) {
    vi A(a);
    vi ans;
    while(sz(A) >= sz(b)) {
        auto cur = bp(b.back(), MOD - 2, MOD);
        ans.pb(mul(A.back(), cur, MOD));
        if(ans.back()) {
            FER(i, 0, sz(b)) {
                auto valor = mul(ans.back(), b[sz(b) - i - 1], MOD);
                A[sz(A) - i - 1] = rem(A[sz(A) - i - 1], valor, MOD);
            }
        }
        A.pop_back();
    }
    reverse(all(ans));
    return make_pair(ans, A);
}
inline pair<vi, vi> divmod(vi a, vi b) {
    if(sz(a) < sz(b)) return {{0}, a};
    ll d = sz(a) - sz(b);
    if(min(d, sz(b)) < 129) return divmod_slow(a, b);
    auto D = reverse_it(mod_xk(reverse_it(a, d + 1) * inverse(reverse_it(b, d + 1), d + 1), d + 1), d + 1, 1);
    return make_pair(D, a - D * b);
}
vi operator % (vi a, vi t) { return divmod(a, t).ss;}
inline void build(ll v, ll l, ll r, vi vec) {
    if(l == r) {
    	T[v] = {rem(0, vec[l], MOD), 1};
        return;
    }
    ll mid = (l + r) >> 1;
    build(v << 1, l, mid, vec);
    build(v << 1 | 1, mid + 1, r, vec);
    T[v] = T[v << 1] * T[v << 1 | 1];
}
inline ll eval(vi a, ll x) {
    ll ans = 0;
    IFR(i, sz(a) - 1, 0) {
    	ans = add(a[i], mul(ans, x, MOD), MOD);
    }
    return ans;
}
inline vi eval(vi a, ll v, ll l, ll r, vi &vec) {
    if(l == r) return {eval(a, vec[l])};
    ll mid = (l + r) >> 1;
    auto A = eval(a % T[v << 1], v << 1, l, mid, vec);
    auto B = eval(a % T[v << 1 | 1], v << 1 | 1, mid + 1, r, vec);
    A.insert(A.end(), B.begin(), B.end());
    return A;
}
inline vi eval(vi &a, vi &x) {
    ll n = sz(x);
    if(is_zero(a)) return vi(n, 0);
    vector<vi>().swap(T);
    T.resize(n << 2);
    build(1, 0, n - 1, x);
    return eval(a, 1, 0, n - 1, x);
}

inline vi chirpz_even(vi a, ll z, ll n) {
    ll m = sz(a) - 1;
    if(is_zero(a)) return vi(n, 0);
    vi vv(m + n);
    ll iz = bp(z, MOD - 2, MOD), zz = mul(iz, iz, MOD), cur = iz, total = 1;
    FER(i, 0, max(n - 1, m) + 1) {
        if(i <= m) vv[m - i] = total;
        if(i < n) vv[m + i] = total;
        total = mul(total, cur, MOD);
        cur = mul(cur, zz, MOD);
    }
    auto w = mul_sq(substr(mul_sq(a, z) * vv, m, m + n), z);
    vi ans(n);
    FER(i, 0, n) ans[i] = w[i];
    return ans;
}

inline vi chirpz(vi a, ll z, ll n) {
    auto even = chirpz_even(a, z, (n + 1) >> 1);
    auto odd = chirpz_even(mulx(a, z), z, n >> 1);
    vi ans(n);
    FER(i, 0, n >> 1) {
        ans[i << 1] = even[i];
        ans[i << 1 | 1] = odd[i];
    }
    if(n & 1) ans[n - 1] = even.back();
    return ans;
}

int main() {
    fastio;
    vi a = {1, 2, 9, 2, 3, 1};
    ll p = 1000000007, base = 10;
    auto values1 = chirpz(a, base, p);
    return 0;
}