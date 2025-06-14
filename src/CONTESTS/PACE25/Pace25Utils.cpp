//
// Created by sylwe on 04/03/2025.
//

#include "Pace25Utils.h"

#include <StandardUtils.h>


atomic<ULL> IntGenerator::last_seed = 0;

array<IntGenerator::seed_type,IntGenerator::K> IntGenerator::seed_sets = createSeedSets();

VI findReachableNodesFromSWithinDistanceK( VVI & V, VI S, int K ) {
    int N = V.size();
    int inf = 1e9;
    VI dst(N,inf);

    for(int d : S) dst[d] = 0;
    vector<bool> was(N);
    for(int d : S) was[d] = true;

    for( int i=0; i<S.size(); i++ ) {
        int v = S[i];
        if(dst[v] >= K) continue;
        was[v] = true;
        for( int d : V[v] ) {
            if(!was[d] && dst[v] + 1 <= K) {
                was[d] = true;
                dst[d] = dst[v] + 1;
                S.push_back(d);
            }
        }
    }

    for(int d : S) assert(dst[d] <= K);

    VI res;
    for(int i=0; i<N; i++) if( dst[i] <= K ) res.push_back(i);
    return res;
}

VI findReachableNodesFromSWithinDistanceK( VVI & V, VI S, int K, VI & dst, VB & was ) {
    int N = V.size();
    if(K == 1) {
        VI res = S;
        for( int d : S ) was[d] = true;
        for(int v : S) for(int d : V[v]) if(!was[d]){ was[d] = true; res.push_back(d); }
        for(int v : res) was[v] = false;
        return res;
    }else if( K == 2 ) {
        VI res = S;
        for( int d : S ) was[d] = true;
        for(int v : S) for(int d : V[v]) {
            if(!was[d]){ was[d] = true; res.push_back(d); }
            for( int dd : V[d] ) if(!was[dd]){ was[dd] = true; res.push_back(dd); }
        }
        for(int v : res) was[v] = false;
        return res;
    }

    for(int d : S) dst[d] = 0;
    for(int d : S) was[d] = true;

    for( int i=0; i<S.size(); i++ ) {
        int v = S[i];
        // if(dst[v] >= K) continue;
        was[v] = true;
        for( int d : V[v] ) {
            if(!was[d] && dst[v] + 1 <= K) {
                was[d] = true;
                dst[d] = dst[v] + 1;
                S.push_back(d);
            }
        }
    }

    for(int d : S) {
        dst[d] = inf;
        was[d] = false;
    }
    return S;
}

VI findFurthestUnreachableNodes( VVI & V, VI S, int K, VB & hit_nodes, int max_unreachables ) {
    int N = V.size();
    VI dst(N,inf);

    for(int d : S) dst[d] = 0;
    vector<bool> was(N);
    for(int d : S) was[d] = true;

    for( int i=0; i<S.size(); i++ ) {
        int v = S[i];
        was[v] = true;
        for( int d : V[v] ) {
            if(!was[d]) {
                was[d] = true;
                dst[d] = dst[v] + 1;
                S.push_back(d);
            }
        }
    }

    VI res;
    int M = K+1;
    for(int i=0; i<N; i++) {
        if( dst[i] > K && ( res.empty() || dst[i] < inf || max_unreachables == inf ) ) res.push_back(i);
    }
    sort(ALL(res), [&](int a, int b){ return dst[a] > dst[b]; });

    if(res.size() > max_unreachables) res.resize(max_unreachables);
    return res;
}


VI findUnreachableNodesWithLargestDegree( VVI & V, VI S, int K, VB & hit_nodes, int max_unreachables, bool include_furthest  ) {
    int N = V.size();
    int inf = 1e9;
    VI dst(N,inf);

    VI res;
    if(K > 1 || include_furthest) {
        for(int d : S) dst[d] = 0;
        vector<bool> was(N);
        for(int d : S) was[d] = true;

        for( int i=0; i<S.size(); i++ ) {
            int v = S[i];
            was[v] = true;
            for( int d : V[v] ) {
                if(!was[d]) {
                    was[d] = true;
                    dst[d] = dst[v] + 1;
                    S.push_back(d);
                }
            }
        }

        constexpr bool exclude_hit_nodes = true;

        int M = K+1;
        for(int i=0; i<N; i++) {
            if constexpr (exclude_hit_nodes)
                if(hit_nodes[i]) continue;

            if( dst[i] > M ) {
                // M = dst[i];
                // res.clear();
                res.push_back(i);
            }
            else if(dst[i] == M && dst[i] < inf) res.push_back(i);
        }
    }else {
        constexpr bool exclude_hit_nodes = true;

        // for(int i=0; i<N; i++) assert(!V[i].empty());
        // clog << "TUTAJ" << endl;
        VB was(N);
        for(int d : S) { was[d] = true; dst[d] = 0; }
        for(int d : S) {
            for(int dd : V[d]) if(!was[dd]) {
                was[dd] = true;
                dst[dd] = 1;
            }
        }
        res.reserve(N);
        for( int i=0; i<N; i++ ) if(!was[i] && ( !hit_nodes[i] || !exclude_hit_nodes) ) res.push_back(i);
    }



    IntGenerator rnd;
    auto shuffle = [&rnd](VI & r) {
        // StandardUtils::shuffle(r);
        for( int i=(int)r.size()-1; i>=0; i-- ){
            int ind = rnd.nextInt(i+1);
            swap( r[i], r[ind] );
        }
    };

    // StandardUtils::shuffle(res,rnd);
    shuffle(res);

    bool add_assortment = true;
    if(add_assortment){
        VI res2;
        VB was(N);

        auto add = [&]( int n ) {
            int cnt = 0;
            for( int i=0; i<res.size() && cnt < n; i++ ) {
                int v = res[i];
                if(!was[v]) {
                    was[v] = true;
                    res2.push_back(v);
                    cnt++;
                }
            }
        };

        // int n = max_unreachables / 8;
        int n = (max_unreachables+5) / 6;


        if( rnd.nextInt(4) ) {
            sort(ALL(res), [&](int a, int b){ return dst[a] > dst[b]; });
            add(n);
        }

        if( rnd.nextInt(4) ) {
            sort(ALL(res), [&](int a, int b){ return dst[a] < dst[b]; });
            add(n);
        }

        if( rnd.nextInt(4) ) {
            sort(ALL(res), [&](int a, int b){ return V[a].size() > V[b].size(); });
            add(n);
        }

        if( rnd.nextInt(4) ) {
            sort(ALL(res), [&](int a, int b){ return V[a].size() < V[b].size(); });
            add(n);
        }

        // StandardUtils::shuffle(res);
        shuffle(res);
        add(max_unreachables - res2.size());

        swap(res,res2);

        // StandardUtils::makeUnique(res);
        fill(ALL(was),false);
        for( int i=(int)res.size()-1; i>=0; i-- ) {
            int a = res[i];
            if(was[a]) REM(res,i);
            was[a] = true;
        }
        // StandardUtils::shuffle(res);
        shuffle(res);
    }
    // sort(ALL(res), [&](int a, int b){ return dst[a] > dst[b]; });
    // sort(ALL(res), [&](int a, int b){ return V[a].size() > V[b].size(); });
    // reverse(ALL(res)); // #TEST - now we have nodes with smallest degree first...

    if(res.size() > max_unreachables) res.resize(max_unreachables);
    return res;
}

volatile sig_atomic_t tle = 0;

void terminate(int signum) { tle = 1; }

void addSigtermCheck(){
    struct sigaction action;
    memset(&action, 0, sizeof(struct sigaction));
    action.sa_handler = terminate;
    sigaction(SIGTERM, &action, NULL);
}