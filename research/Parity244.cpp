// Exact optima at a given overlap with the canonical 32-point even core.
// g++ -O3 -std=c++20 Parity244.cpp -o parity244 && ./parity244 6
#include <algorithm>
#include <bit>
#include <bitset>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <vector>
using namespace std;
constexpr int N = 244;
using Set = bitset<N>;

struct Search {
    vector<int> core;
    vector<int> outside;
    vector<vector<uint32_t>> blocked = vector<vector<uint32_t>>(N);
    Set complete, winner;
    unsigned long long masks = 0;
    int best = 0;

    Search() {
        core = {0};
        for (int p = 1; p <= 81; p *= 3) {
            auto old = core;
            for (int x : old) core.push_back(x + 2*p);
        }
        for (int x : core) complete.set(x);
        for (int x=0; x<N; ++x) if (!complete[x]) outside.push_back(x);
        for (int i=0; i<32; ++i) for (int j=0; j<i; ++j) {
            const int x=core[j], y=core[i];
            const auto pair = (uint32_t(1)<<i) | (uint32_t(1)<<j);
            for (int z : {2*x-y, 2*y-x, (x+y)/2})
                if (z>=0 && z<N) blocked[z].push_back(pair);
        }
    }

    static bool compatible(int x, int y, const Set &fixed) {
        if (x>y) swap(x,y);
        return !((2*x>=y && fixed[2*x-y]) || (2*y-x<N && fixed[2*y-x]) ||
                 ((x+y)%2==0 && fixed[(x+y)/2]));
    }

    // Partition viable sites into groups whose members conflict pairwise.
    // Any extension uses at most one site per group.
    static int colourBound(const Set &fixed, const vector<int> &choices, int cutoff) {
        vector<vector<int>> groups;
        for (int x : choices) {
            bool placed=false;
            for (auto &group : groups) {
                if (none_of(group.begin(),group.end(),[&](int y){return compatible(x,y,fixed);})) {
                    group.push_back(x); placed=true; break;
                }
            }
            if (!placed) {
                groups.push_back({x});
                if (int(groups.size())>=cutoff) return cutoff;
            }
        }
        return int(groups.size());
    }

    void extend(Set &fixed, int size, const vector<int> &choices) {
        if (size>best) {best=size; winner=fixed;}
        if (size+int(choices.size())<=best) return;
        if (choices.size()>=7 && size+colourBound(fixed,choices,best-size+1)<=best) return;
        for (size_t i=0; i<choices.size(); ++i) {
            if (size+int(choices.size()-i)<=best) return;
            int x=choices[i];
            vector<int> next;
            for (size_t j=i+1;j<choices.size();++j)
                if (compatible(x,choices[j],fixed)) next.push_back(choices[j]);
            fixed.set(x);
            extend(fixed,size+1,next);
            fixed.reset(x);
        }
    }

    void examine(uint32_t deleted) {
        ++masks;
        vector<int> choices;
        for (int x : outside) {
            bool ok=true;
            for (auto edge : blocked[x]) if (!(edge & deleted)) {ok=false;break;}
            if (ok) choices.push_back(x);
        }
        int size=32-popcount(deleted);
        if (size+int(choices.size())<=best) return;
        Set fixed=complete;
        for (int i=0;i<32;++i) if ((deleted>>i)&1) fixed.reset(core[i]);
        extend(fixed,size,choices);
    }

    void choose(int lo, int remaining, uint32_t deleted) {
        if (!remaining) {examine(deleted);return;}
        for (int i=lo;i<=32-remaining;++i)
            choose(i+1,remaining-1,deleted|(uint32_t(1)<<i));
    }

    void run(int missing) {
        masks=0; best=0; winner.reset();
        choose(0,missing,0);
        if (int(winner.count())!=best || (winner&complete).count()!=size_t(32-missing))
            throw runtime_error("witness cardinality");
        for (int a=0;a<N;++a) for (int d=1;a+2*d<N;++d)
            if (winner[a] && winner[a+d] && winner[a+2*d]) throw runtime_error("progression");
        cout << "missing " << missing << ", masks " << masks << ", maximum " << best << ", witness";
        for (int i=0;i<N;++i) if (winner[i]) cout << " " << i;
        cout << endl;
    }
};
int main(int argc, char **argv) {
    int limit=argc>=2 ? stoi(argv[1]) : 6;
    if (limit<0 || limit>32) return 1;
    Search search;
    int first=argc>=3 ? stoi(argv[2]) : 0;
    if (first<0 || first>limit) return 1;
    for (int i=first;i<=limit;++i) search.run(i);
}
