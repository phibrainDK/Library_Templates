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


typedef int ll;
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

const int B = 275;
const int LP = (100000 / B) + 5;
struct T {
    ll sz, link, nxt[26];
    T() {}
    inline void clear() {
        FER(i, 0, 26) nxt[i] = 0;
    }
};

struct SA {
    T t[B << 1];
    ll cnt[B << 1], End[B << 1], nod, last;
    inline void preprocess(ll n) {
        FER(i, 0, n << 1) {
            t[i].clear();
            cnt[i] = -1;
            End[i] = 0;
        }
        t[0].sz = 0;
        t[0].link = -1;
        nod = 1;
        last = 0;
    }
    inline void add(char ch) {
        auto c = (ll) (ch - 'a');
        ll cur = nod ++;
        t[cur].sz = t[last].sz + 1;
        auto p = last;
        while(p != -1 and !t[p].nxt[c]) {
            t[p].nxt[c] = cur;
            p = t[p].link;
        }
        if(p == -1) t[cur].link = 0;
        else{
            auto q = t[p].nxt[c];
            if(t[p].sz + 1 == t[q].sz) t[cur].link = q;
            else{
                auto x = nod ++;
                t[x].sz = t[p].sz + 1;
                FER(i, 0, 26) t[x].nxt[i] = t[q].nxt[i];
                t[x].link = t[q].link;
                while(p != -1 and t[p].nxt[c] == q) {
                    t[p].nxt[c] = x;
                    p = t[p].link;
                }
                t[q].link = t[cur].link = x;
            }
        }
        last = cur;
    }
    inline ll dfs(ll u) {
		if(cnt[u] != -1) return cnt[u];
        cnt[u] = End[u];
        FER(i, 0, 26) if(t[u].nxt[i]) {
            cnt[u] += dfs(t[u].nxt[i]);
        }
        return cnt[u];
    }
    inline void push() {
        auto cur = last;
        while(cur > 0) {
            End[cur] = 1;
            cur = t[cur].link;
        }
    }
    inline ll que(string &s) {
        ll cur = 0;
        for(auto xdt : s) {
            auto xd = (ll) (xdt - 'a');
            if(!t[cur].nxt[xd]) return 0;
            else cur = t[cur].nxt[xd]; 
        }
        return dfs(cur);
    } 
}st[LP];

int main() {
    fastio;
    // https://codeforces.com/contest/914/problem/F
    string s; cin >> s;
    ll n = sz(s);
    ll q, ty, l, r; cin >> q;
    char ch;
    string cur;
    FER(i, 0, ((n - 1) / B) + 1) st[i].preprocess(B);
    FER(i, 0, n) st[i / B].add(s[i]);
	FER(i, 0, ((n - 1) / B) + 1) st[i].push();
    auto Upd = [&](ll p, char ch) {
        s[p] = ch;
        auto id = p / B;
        st[id].preprocess(B);
        FER(i, id * B, min(n, (id + 1) * B)) st[id].add(s[i]);
        st[id].push();
    };
    auto kmp = [&](vector<short int> &sq, ll m) {
        vi p(sz(sq));
        p[0] = 0;
        ll ans = 0;
        FER(i, 1, sz(sq)) {
            p[i] = p[i - 1];
            while(p[i] and sq[p[i]] != sq[i]) p[i] = p[p[i] - 1];
            if(sq[p[i]] == sq[i]) p[i] ++;
            ans += p[i] == m;
        }
        return ans;
    };
    auto Q = [&](ll l, ll r, string &sq) {
        if(sz(sq) > r - l) return (ll) 0;
        ll n = sz(sq), ans = 0;
        vector<short int> vec;
    	for(auto xd : sq) vec.pb(xd - 'a');
    	vec.pb(-1);
        FER(i, l, r) vec.pb(s[i] - 'a');
        return kmp(vec, n);
    };
    auto Que = [&](ll l, ll r, string &sq) {
        if(sz(sq) >= B or (r - l) <= (B << 1)) return Q(l, r, sq);
		ll ans = 0, slash = -1, m = sz(sq);
        vector<short int> vec;
        for(auto xd : sq) vec.pb(xd - 'a');
        vec.pb(slash --);
        FER(i, l, ((l / B) + 1) * B + sz(sq) - 1) vec.pb(s[i] - 'a');
        vec.pb(slash --);
        FER(i, ((r - 1) / B) * B - sz(sq) + 1, r) vec.pb(s[i] - 'a');
        vec.pb(slash --);
        FER(i, (l / B) + 1, (r - 1) / B) {
            auto k1 = st[i].que(sq);
            if(i + 1 != (r - 1) / B) {
            	ll l = (i + 1) * B - sz(sq) + 1;
	            ll r = (i + 1) * B + sz(sq) - 1;        
                FER(j, l, r) vec.pb(s[j] - 'a');
                vec.pb(slash --);
            }
            ans += k1;
        }
        ans += kmp(vec, m);
        return ans;
    };
    FER(i, 0, q) {
        cin >> ty;
        if(ty & 1) {
            cin >> l >> ch; l --;
            Upd(l, ch);
        }
        else{
            cin >> l >> r >> cur; l --;
            auto HinaChan = Que(l, r, cur);
            cout << HinaChan << "\n";
        }
    }
    return 0;
}