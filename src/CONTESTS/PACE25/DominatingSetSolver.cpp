//
// Created by sylwe on 04/03/2025.
//

#include "DominatingSetSolver.h"

#include <CombinatoricUtils.h>
#include <GraphInducer.h>
#include <GraphUtils.h>
#include <VertexCover/approximation/NuMVC/NuMVC.h>
#include <StandardUtils.h>
#include <Stopwatch.h>
#include <components/ConnectedComponents.h>

#include "CollectionOperators.h"
#include "DSSE.h"
#include "GraphRemapper.h"
#include "HittingSetLS.h"

#include "Pace25Utils.h"
#include "VertexCover/VCUtils.h"
#include "VertexCover/approximation/LibMVC/fastvc.h"



void DSS::fillGreedilyToValidSolution(VVI & V, VI &hs, int K, VB &hit_nodes) {
    int N = V.size();
    VB was(N);
    VI dst(N,inf);
    auto reachable = findReachableNodesFromSWithinDistanceK(V, hs, K, dst,was );

    VB hit(N);
    for(int d : reachable) hit[d] = true;
    VI perm = CombinatoricUtils::getRandomPermutation(N);

    // sort(ALL(perm), [&](auto a, auto b){ return V[a].size() > V[b].size(); });
    // #TEST - sorting may decrease variability...

    int block_size = 5;
    VI to_add;
    auto addNodes = [&]() {
        reachable = findReachableNodesFromSWithinDistanceK( V, to_add, K, dst,was );
        hs += to_add;
        to_add.clear();
        for(int d : reachable) hit[d] = true;
    };
    for( int d : perm ) if(!hit[d] && !hit_nodes[d]) {
        to_add.push_back(d);
        if( (to_add.size() % block_size == 0) ) addNodes();
    }
    if(!to_add.empty()) addNodes();
}

bool DominatingSetSolver::isVCCase(VVI &V, VB &hit) {
    int N = V.size();

    // DEBUG(GraphUtils::isBipartite(V));
    if( !GraphUtils::isBipartite(V) ) return false; // graph must be bipartite

    int deg2_nodes = 0;
    int hit_deg2_nodes = 0;
    for(int i=0; i<V.size(); i++) deg2_nodes += (V[i].size() == 2);
    for(int i=0; i<V.size(); i++) hit_deg2_nodes += hit[i] && (V[i].size() == 2);


    int deg2_nodes_with_both_ends_hit = 0;
    int deg2_nodes_with_at_least_one_end_hit = 0;
    for(int i=0; i<V.size(); i++) if( V[i].size() == 2 && !hit[i] ) {
        int a = V[i][0], b = V[i][1];
        deg2_nodes_with_both_ends_hit += hit[a] && hit[b];
        deg2_nodes_with_at_least_one_end_hit += hit[a] || hit[b];
    }
    int deg2_nodes_with_one_end_hit = deg2_nodes_with_at_least_one_end_hit - deg2_nodes_with_both_ends_hit;

    // DEBUG(deg2_nodes);
    // DEBUG(hit_deg2_nodes);
    // DEBUG(deg2_nodes_with_at_least_one_end_hit);
    // DEBUG(deg2_nodes_with_both_ends_hit);
    // DEBUG(deg2_nodes_with_one_end_hit);

    // if( deg2_nodes_with_at_least_one_end_hit != deg2_nodes ) return false;
    if( deg2_nodes_with_both_ends_hit != deg2_nodes ) return false;

    bool all_nondeg2_incident_to_only_deg2 = true;
    for( int i=0; i<N; i++ ) if( V[i].size() != 2 ) {
        for(int d : V[i]) all_nondeg2_incident_to_only_deg2 &= (V[d].size() == 2);
    }

    return all_nondeg2_incident_to_only_deg2;
}

tuple<VVI,VI,VI> DominatingSetSolver::transformToVC(VVI &V, VB &hit) {
    int N = V.size();

    int N2 = N;
    // for( int i=0; i<N; i++ ) if( V[i].size() == 2 && !hit[i] ) {
    for( int i=0; i<N; i++ ) if( V[i].size() == 2 ) {
        int a = V[i][0], b = V[i][1];
        N2 -= hit[a] && hit[b];
    }

    VI mapper(N,-1);
    VI remapper(N2, -1);
    int cnt = 0;

    auto addToMapper = [&](int a) {
        if(mapper[a] == -1) {
            mapper[a] = cnt;
            remapper[cnt] = a;
            cnt++;
        }
    };

    VPII edges; edges.reserve(N);
    // for( int i=0; i<N; i++ ) if( V[i].size() == 2 && !hit[i] ) {
    for( int i=0; i<N; i++ ) if( V[i].size() == 2 ) {
        int a = V[i][0], b = V[i][1];
        addToMapper(a);
        addToMapper(b);
        a = mapper[a];
        b = mapper[b];
        if(a > b) swap(a,b);
        assert(a != b); // this need not hold - it might be a == b, this is just to check if such a case occurs in tests
        // zb.insert({a,b});
        edges.emplace_back(a,b);
    }

    VVI W(cnt);
    StandardUtils::makeUnique(edges);
    for(auto [a,b] : edges) GraphUtils::addEdge(W,a,b);
    assert(cnt == N2);

    for(auto x : remapper) assert(x != -1 && x < N);
    for ( int i=0; i<N; i++ ) if ( mapper[i] != -1 ) {
        assert(remapper[mapper[i]] == i);
    }
    cnt = 0;
    for(int i=0; i<N; i++) cnt += (mapper[i] != -1);
    assert(cnt == N2);

    return {W,mapper,remapper};
}

tuple<VI,VB,VB,VI,vector<LiftableRule*>> DominatingSetSolver::reductionRulesDS(VVI & V, int time_limit_millis,
     const bool only_basic_reductions) {

    DSReducer red(hit_nodes, excluded_nodes);
    red.recursive_reductions_level = recursion_level; // setting this to prevent logs and some time-consuming rules
    // on higher levels of recursion
    red.setPermanentExcludedNodeUnhitDominator(permanent_excluded_node_unhit_dominator);
    return red.reductionRulesDS(V, time_limit_millis, only_basic_reductions);

}



VI DSS::ds21swaps( VVI & V, VI hs, double small_iters_scale, int max_large_iters, bool enable_21_swaps, int K ) {
    if( hs_track ) return hs;

    int N = V.size();
    VB was(N);

    int hs_size_before = hs.size();

    VB res(N);
    for(int d : hs) res[d] = true;
    if(hit_nodes.empty()) hit_nodes = VB(N);

    assert(isCorrect(V,hs,1,hit_nodes));

    VB helper(N);
    VI dst(N,inf);

    VI covered_by(N,0);
    for( int d : hs ) {
        covered_by[d]++;
        for(int dd : V[d]) covered_by[dd]++;
    }

    VI hits_uncovered(N,0);
    int uncovered = 0;

    auto rem = [&](int v) {
        if( !hit_nodes[v] && --covered_by[v] == 0 ) {
            uncovered++;
            hits_uncovered[v]++;
            for( int dd : V[v] ) hits_uncovered[dd]++;
        }

        for( int d : V[v] ) {
            if( !hit_nodes[d] && --covered_by[d] == 0) {
                uncovered++;
                hits_uncovered[d]++;
                for( int dd : V[d] ) hits_uncovered[dd]++;
            }
        }

        res[v] = false;
    };

    auto add = [&]( int v ) {
        if(!hit_nodes[v] && covered_by[v]++ == 0) {
            uncovered--;
            hits_uncovered[v]--;
            for( int dd : V[v] ) hits_uncovered[dd]--;
        }
        for( int d : V[v] ) {
            if( !hit_nodes[d] && covered_by[d]++ == 0 ) {
                uncovered--;
                hits_uncovered[d]--;
                for( int dd : V[d] ) hits_uncovered[dd]--;
            }
        }
        res[v] = true;
    };

    IntGenerator rnd;

    unordered_map<int, VI> cached_neighs;
    auto getNeigh = [&](int v, int K = 2)
    {
        VI NEIGH;
        if( cached_neighs.contains(v) ) NEIGH = cached_neighs[v];
        else{
            NEIGH = findReachableNodesFromSWithinDistanceK(V,{v}, K, dst, helper);
            cached_neighs[v] = NEIGH;
            constexpr int MAX_CACHE_SIZE = 10'000;
            if( cached_neighs.size() > MAX_CACHE_SIZE ) cached_neighs.erase( cached_neighs.begin() );
        }
        return NEIGH;
    };

    bool changes = true;
    int large_iters = 0;
    while((changes || large_iters < max_large_iters) && !sw.tle()) {
        changes = false;
        // bool enable_21_swaps = false;
        // bool enable_21_swaps = ( large_iters > 0 );

        deque<int> que(ALL(hs));
        int iters = 0;
        VB in_queue(N);
        for(int d : hs) in_queue[d] = true;

        VI perm = CombinatoricUtils::getRandomPermutation(N);

        // clog << "\rMaking 2-1 / 1-1 swaps, iter: " << large_iters +1 << " / " << max_large_iters << flush;

        VB conf_check(N, false);
        for( int d : hs ) conf_check[d] = true;

        // while( !que.empty() ){
        while( !que.empty() && (iters++ < 1ll * small_iters_scale * hs.size()) && !sw.tle() ){
            int v = que.front();
            que.pop_front();
            in_queue[v] = false;
            if( !res[v] ) continue;
            if( !conf_check[v] ) continue;

            {
                // const int R = 1 + N / hs.size();
                const int R = 5;
                // const int R = pow(N,0.33);
                // const int R = pow(N,0.5);
                // const int R = pow(N,0.66);
                // const int R = pow(N,0.75);
                // const int R = N/10;
                for(int i=0; i<R; i++) {
                    // int a = rnd.nextInt(N);
                    int a = hs[rnd.nextInt(hs.size())];
                    int b = rnd.nextInt(N);
                    swap(perm[a], perm[b]);
                }
            }

            // constexpr int K = 2;
            if(!K) K = 2;
            else K = 1;
            // auto NEIGH = findReachableNodesFromSWithinDistanceK(V,{v}, K, dst, helper);
            auto NEIGH = getNeigh(v,K);

            // int vv = -1,uu = -1,ww = -1;

            uncovered = 0;
            bool can_make_swap = false;
            rem(v);
            // clog << "v: " << v << ", uncovered: " << uncovered << endl;
            swap(perm[rnd.nextInt(N)], perm[v]); // changing perm of node

            if(uncovered) {
                if( enable_21_swaps ) {
                    for(int d : V[v]) was[d] = true; // mark neighborhood of v

                    for( int u : NEIGH ) {
                        // if( rnd.nextInt(5) ) continue;
                        // if( !enable_21_swaps ) break; // #TEST - only 1-1 swaps and removing redundant nodes...
                        if( u == v || !res[u] ) continue;
                        // clog << "\tu: " << u << endl;

                        // check if there exists a 2-1-swap (v,u) -> (w)
                        rem(u);

                        for( int w : V[u] ) if(was[w]) { // w must be a common neighbor of u and v
                            if( hits_uncovered[w] == uncovered ) {
                                can_make_swap = true;
                                // res[v] = res[w] = false; res[w] = true;
                                add(w);
                                changes = true;
                                if(!in_queue[w]) {
                                    que.push_back(w);
                                    in_queue[w] = true;
                                }

                                // clog << "Found a 2-1 swap, swapping(" << v << "," << u << ") to " << w <<  "" << endl;
                                // DEBUGV(V,v);
                                // DEBUGV(V,u);
                                // DEBUGV(V,w);
                                break;
                            }
                        }

                        if( can_make_swap  ) break;

                        add(u);

                        // { // #TEST - just an assertion
                        //     add(v);
                        //     auto r = StandardUtils::toVI(res);
                        //     assert( isCorrect(V,r,1) );
                        //     rem(v);
                        // }
                    }

                    for(int d : V[v]) was[d] = false; // unmark neighborhood of
                }

                auto cmp = [&](int a, int b) {
                    // if(rnd.nextInt(5) == 0) {
                    //     if(V[a].size() != V[b].size()) return V[a].size() < V[b].size();
                    //     if( covered_by[a] != covered_by[b] ) return covered_by[a] < covered_by[b];
                    // }
                    if( conf_check[a] != conf_check[b] ) return (bool) conf_check[a];
                    return perm[a] < perm[b];
                };

                int to_add = -1;
                if(!can_make_swap) {
                    constexpr bool can_add_excluded_node = true; // default = true (seems to work better)

                    ULL val = 0;
                    // for( int u : NEIGH ) if( u != v && hits_uncovered[u] == uncovered ) {
                    // for( int u : NEIGH ) if( hits_uncovered[u] == uncovered ) { // original
                    for( int u : NEIGH ) if( (hits_uncovered[u] == uncovered)
                        && ( can_add_excluded_node || !excluded_nodes[u] || u == v ) ) { // #TEST
                        ULL newval = rnd.rand();
                        bool cond = ( newval >= val );
                        // cond = (to_add == -1) || cmp(to_add,u); // original
                        // #CAUTION #TEST - originally, the line above was uncommented, but for h070
                        // it works much better when only newval >= val condition is used
                        // cond = (to_add == -1) || (cmp(to_add,u) && to_add != v) || (to_add == v);
                        if (rnd.nextInt(4) <= 2) cond = ((to_add == -1) || cmp(to_add,u));

                        if(cond) { to_add = u; val = newval; }
                    }

                    assert(to_add != -1);
                    assert(hits_uncovered[to_add] == uncovered);
                    add(to_add);
                    swap(perm[rnd.nextInt(N)], perm[to_add]); // changing perm of node
                    {
                        // NEIGH = findReachableNodesFromSWithinDistanceK(V,{to_add}, K, dst, helper);
                        NEIGH = getNeigh(to_add,K);
                        conf_check[to_add] = true;
                        conf_check[v] = true;
                        for( int d : NEIGH ) if( res[d] && d != v && d != to_add ) conf_check[d] = true;

                        // for( int d : NEIGH ) if( res[d] && d != to_add ) conf_check[d] = true;
                        // for( int d : NEIGH ) if( res[d] && d != v ) conf_check[d] = true;
                    }
                    if(!in_queue[to_add]) {
                        que.push_back(to_add);
                        in_queue[to_add] = true;
                    }
                }

                // if(!can_make_swap) add(v);
            }else {
                // clog << "\tFound a redundant node v: " << v << endl;
                conf_check[v] = false;
            }

            // { // #TEST
            //     auto r = StandardUtils::toVI(res);
            //     assert( isCorrect(V,r,1) );
            // }
        }

        { // #TEST
            auto r = StandardUtils::toVI(res);
            // assert( isCorrect(V,r, 1) );
            assert( isCorrect(V,r, 1, hit_nodes) );
        }

        hs = StandardUtils::toVI(res);
        // DEBUG(hs.size());
        // if(changes) ENDL(2);
        large_iters++;
    }

    // DEBUG(hs_size_before);
    // DEBUG(hs.size());
    // DEBUG(large_iters);
    // clog << "swaps done: " << hs_size_before - hs.size() << endl;

    return hs;
}

VI DominatingSetSolver::ds21swapsGRASP(VVI &V, VI hs, int K, bool use_perpetually_small_iterations) {
    int N = V.size();

    VVI W(N);
    VI dst(N,inf);
    VB was(N);
    for(int i=0; i<N; i++) {
        auto reachables = findReachableNodesFromSWithinDistanceK(V, {i}, K, dst, was);
        W[i].reserve(reachables.size());
        for(int d : reachables) if(d != i) W[i].push_back(d);
    }
    swap(W,V);
    K = 1;

    VI res = move(hs);
    VB hit_nodes(N);
    DSS::fillGreedilyToValidSolution(V, res, K, hit_nodes);
    if constexpr (enable_logs) DEBUG(res.size());
    int iters_without_improvements = 0;

    auto perturb = [&]() {
        iters_without_improvements = 0;
        {
            // double F = 0.03;
            double F = 0.07;
            auto & S = res;
            StandardUtils::shuffle(S);
            // clog << "No improvement found, removing random " << 100*F << "% nodes from S" << endl;
            int new_S_size = (int)((1.0-F) * S.size());
            new_S_size = min( new_S_size, max( 1, (int)S.size()-5 ) );
            S.resize( new_S_size );
            DSS::fillGreedilyToValidSolution(V, S, K, hit_nodes);
        }
    };

    VI best_res = res;

    int THR = ( use_perpetually_small_iterations ? 1e9 : 50 );
    for( int i=1; i<THR && !sw.tle(); i++ ) {
        // res = dss.ds21swaps(V,res, i, 3, false, 2);

        int prev = res.size();
        // res = ds21swaps(V,res, 3, 1+(i%10), false, 2);
        res = ds21swaps(V,res, 1, 1+(i%10), false, 2);
        if( prev == res.size() ) iters_without_improvements++;
        if(iters_without_improvements == 30) perturb();

        if( res.size() < best_res.size() ) {
            best_res = res;
            iters_without_improvements = 0;
        }

        // DEBUG(best_res.size());
    }
    if constexpr (enable_logs) DEBUG(res.size());
    if constexpr (enable_logs) DEBUG(best_res.size());



    while(!sw.tle()) {
        // DEBUG(best_res.size());
        int prev = res.size();
        // res = ds21swaps(V,res, 3, 50, false, 2);
        res = ds21swaps(V,res, 1, 5, false, 2);
        // res = dss.ds21swaps(V,res, 10, 100, false, 2);
        if( prev == res.size() ) iters_without_improvements++;
        if(iters_without_improvements == 30) perturb();
        if( res.size() < best_res.size() ) {
            best_res = res;
            iters_without_improvements = 0;
        }
    }
    if constexpr (enable_logs) DEBUG(best_res.size());

    res = best_res;

    return res;
}

VI DominatingSetSolver::greedyWithReductions(VVI V) {

    vector<LiftableRule*> to_lift;

    int N = V.size();
    VB hit = hit_nodes;
    VB excluded = excluded_nodes;


    auto selectNodeToAdd = [&]() {
        int best_v = 0;

        auto cmp1 = [&](int a, int b) {
            return V[a].size() < V[b].size();
        };

        for( int i=0; i<N; i++ ) {
            // select the largest node with respect to used comparator
            if( cmp1(best_v,i) ) best_v = i;
        }

        return best_v;
    };

    bool only_basic_reductions = false;
    int iter = 0;
    while( GraphUtils::countEdges(V) > 0 ) {
        ENDL(1); iter++; DEBUG(iter);

        DSReducer red(hit, excluded);
        red.recursive_reductions_level = 1;
        auto [kernel, _hit, _excluded, penud, lft] =
            red.reductionRulesDS(V,1'000, only_basic_reductions);

        only_basic_reductions = !only_basic_reductions;
        // only_basic_reductions = ( iter % 5 == 0 ? false : true );

        to_lift += lft;
        hit = _hit;
        excluded = _excluded;

        int v = selectNodeToAdd();
        {
            int covers_unhit = !hit[v];
            for(int d : V[v]) covers_unhit += !hit[d];
            clog << "Removing node " << v << " from the graph with V[" << v << "].size(): " << V[v].size()
                 << " and covers_unhit: " << covers_unhit << endl;
            clog << "\tto_lift.size(): " << to_lift.size() << endl;
        }

        to_lift.push_back(new ReducibleRule(v));
        hit[v] = true;
        for(int d : V[v]) hit[d] = true;
        GraphUtils::removeNodeFromGraph(V,v);

    }

    VB in_res(N);
    reverse(ALL(to_lift));
    for(auto * r : to_lift) {
        r->lift(in_res);
        delete r;
    }

    VI res = StandardUtils::toVI(in_res);
    DEBUG(res.size());
    // exit(1);

    return res;
}

VI DSS::solveH( VVI V, int K, bool use_preprocessing, int time_limit_millis, bool leave_at_K1,
                bool recurse_on_disconnected  ) {

    if(V.empty()) return {};
    {
        bool all_empty = true;
        for (auto & v : V) all_empty &= v.empty();
        // if (all_empty) return {}; // original, but incorrect
        if (all_empty) {
            VI all_nodes;
            for (int i=0; i<V.size(); i++) if ( !hit_nodes[i] ) all_nodes.push_back(i);
            return all_nodes;
        }
    }

    sw.setLimit("main", time_limit_millis);
    sw.reset("main");
    sw.start("main");

    int N = V.size(), M = GraphUtils::countEdges(V);

    auto initV = V;
    // hit_nodes = VB(N);
    // excluded_nodes = VB(N);

    const bool convert_to_K1 = (K > 1);
    if(convert_to_K1){
        VVI W(N);
        VI dst(N,inf);
        VB was(N);
        for(int i=0; i<N; i++) {
            auto reachables = findReachableNodesFromSWithinDistanceK(V, {i}, K, dst, was);
            if (!reachables.empty()) W[i].reserve(reachables.size());
            for(int d : reachables) if(d != i) W[i].push_back(d);
        }
        swap(W,V);

        // bool leave_at_K1 = true;
        if(leave_at_K1){
            K = 1;
            M = GraphUtils::countEdges(V);
            initV = V; // as K changes, we also need to change initV
        }else swap(W,V);

    }

    constexpr bool write_to_file = (false && convert_to_K1);
    if(write_to_file){
        if constexpr (enable_logs) clog << "Writing DS instance to file temp.txt, transformed for K = 1" << endl;
        ofstream str("temp.txt");
        auto edges = GraphUtils::getGraphEdges(V);
        int M = edges.size();
        str << "p edge " << N << " " << M << endl;
        for(auto [a,b] : edges) str << "e " << a+1 << " " << b+1 << '\n';
    }

    if( !hit_nodes.empty() && hit_nodes.size() != N ) hit_nodes.clear();
    if( hit_nodes.empty() ) hit_nodes = VB(N);

    if( !permanent_excluded_node_unhit_dominator.empty() && permanent_excluded_node_unhit_dominator.size() != N )
        permanent_excluded_node_unhit_dominator.clear();
    if ( permanent_excluded_node_unhit_dominator.empty() ) {
        permanent_excluded_node_unhit_dominator = VI(N);
        iota(ALL(permanent_excluded_node_unhit_dominator),0);
    }

    if( !excluded_nodes.empty() && excluded_nodes.size() != N ) excluded_nodes.clear();
    if( excluded_nodes.empty() ) excluded_nodes = VB(N);
    // {
    //     if( recursion_level == 0 ) {
    //         hit_nodes = VB(N);
    //         excluded_nodes = VB(N);
    //     }
    // }

    // auto V0 = V;
    auto & V0 = initV;
    auto hit_nodes_0 = hit_nodes;
    auto excluded_nodes_0 = excluded_nodes;
    auto penud_0 = permanent_excluded_node_unhit_dominator;

    if constexpr (enable_logs) clog << "N: " << N << ", M: " << M << ", K: " << K << endl;

    VI isolated_nodes, nonisolated_nodes;
    InducedGraph g;

    constexpr bool induce_by_nonisolated_nodes = true;
    if constexpr (induce_by_nonisolated_nodes) {
        for(int i=0; i<N; i++) {
            if( V[i].empty() ) isolated_nodes.push_back(i);
            else nonisolated_nodes.push_back(i);
        }
        auto gg = GraphInducer::induce(V, nonisolated_nodes);
        swap(g,gg);
        V = g.V;
        N = V.size();
        M = GraphUtils::countEdges(V);

        if( !hit_nodes.empty() ) {
            VB h;
            if (N) h = VB(N);
            for( int i=0; i<N; i++ ) h[i] = hit_nodes[g.nodes[i]];
            hit_nodes = h;
        }

        if( !excluded_nodes.empty() ) {
            VB e;
            if (N) e = VB(N);
            for( int i=0; i<N; i++ ) e[i] = excluded_nodes[g.nodes[i]];
            excluded_nodes = e;
        }

        if( !permanent_excluded_node_unhit_dominator.empty() ) {
            VI p;
            if (N) {
                p = VI(N);
                iota(ALL(p),0);
            }
            // for( int i=0; i<N; i++ ) p[i] = permanent_excluded_node_unhit_dominator[g.nodes[i]];
            for( int i=0; i<N; i++ ) {
                int w = permanent_excluded_node_unhit_dominator[g.nodes[i]];
                assert(w != -1 && w < initV.size());
                p[i] = (g.perm.contains(w) ? g.perm[w] : i);
                if (permanent_excluded_node_unhit_dominator[g.nodes[i]] == g.nodes[i]) assert( g.perm.contains(w) );
                else if (g.perm.contains(w)) assert(g.perm[w] != i);
            }
            permanent_excluded_node_unhit_dominator = p;
        }

        if constexpr (enable_logs) DEBUG(isolated_nodes.size());
        if constexpr (enable_logs) clog << "N: " << N << ", M: " << M << ", K: " << K << endl;
    }

    // hit_nodes = VB(N);
    // excluded_nodes = VB(N);

    if( hit_nodes.empty() && N ) hit_nodes = VB(N);
    if( excluded_nodes.empty() && N ) excluded_nodes = VB(N);
    if( permanent_excluded_node_unhit_dominator.empty() && N ) {
        permanent_excluded_node_unhit_dominator = VI(N);
        iota(ALL(permanent_excluded_node_unhit_dominator),0);
    }

    VI kernel;
    VB &hit = hit_nodes;
    // hit = VB(N,false);
    VB &excluded = excluded_nodes;
    VI & penud = permanent_excluded_node_unhit_dominator;
    if (penud.empty() && N) {
        penud = VI(N);
        iota(ALL(penud),0);
    }

    auto hit_nodes_1 = hit_nodes;

    InducedGraph g2;
    vector<LiftableRule*> liftable_rules;
    use_preprocessing &= (K == 1);

    constexpr bool use_multilevel_preprocessing = true;
    constexpr int MAX_RECURSION_LEVEL = 1; // default value 0 - only on level zero we recurse into connected components
    assert( recursion_level <= MAX_RECURSION_LEVEL+1 );
    if( recursion_level == MAX_RECURSION_LEVEL+1 ) assert( !recurse_on_disconnected );

    bool finished_preprocessing_in_time_limit = false;


    if(use_preprocessing){
        sw.start("preprocessing");

        // int reductions_limit_millis = time_limit_millis * 0.28; // maximum of 30% of total time, #TEST
        int reductions_limit_millis = time_limit_millis / 4; // maximum of 25% of total time, original
        // const int reductions_limit_millis = time_limit_millis / 5; // maximum of 20% of total time, #TEST
        // const int reductions_limit_millis = time_limit_millis / 6; // maximum of 17% of total time, #TEST
        if(use_multilevel_preprocessing) reductions_limit_millis /= (2 + recursion_level);
        // if (solve_by_cpsat)  reductions_limit_millis = time_limit_millis / 3; // #TEST
        if(hs_track) reductions_limit_millis /= 4;

        tie (kernel,hit, excluded, penud, liftable_rules) = reductionRulesDS(V,reductions_limit_millis);
        if constexpr (enable_logs) clog << "Liftable rules: " << liftable_rules.size() << " rules to lift" << endl;

        bool check_special_cases_loco = false;
        if (check_special_cases_loco){
            {
                VI dominators;
                for ( auto * r : liftable_rules ) {
                    string name = r->getName();
                    if (name == "dom") {
                        DomRed * drr = dynamic_cast<DomRed*>(r);
                        // dominators += drr->dominators;
                        dominators.push_back(drr->swap_to);
                    }
                }
                StandardUtils::makeUnique(dominators);
                clog << "Set of dominators contains " << dominators.size() << " nodes" << endl;

                VVI sets;
                for ( int i=0; i<N; i++ ) if ( !hit[i] && !V[i].empty() ) {
                    sets.push_back(V[i]);
                    sets.back().push_back(i);
                }
                HSLS::fillByHSToValidHS(sets,dominators);
                clog << "After filling to valid HS, dominators.size(): " << dominators.size() << endl;
                // exit(4);
            }

            {
                VPII path3_rules_edges;
                VI path3_rules_node_ends;
                for ( auto * r : liftable_rules ) {
                    string name = r->getName();
                    if (name == "dom_path") {
                        auto * drp = dynamic_cast<DomRedPath*>(r);
                        auto e = drp->to;
                        if (e.first > e.second) swap(e.first, e.second);
                        path3_rules_edges.push_back(e);
                        path3_rules_node_ends.push_back(e.first);
                        path3_rules_node_ends.push_back(e.second);
                    }
                }
                StandardUtils::makeUnique(path3_rules_node_ends);
                StandardUtils::makeUnique(path3_rules_edges);
                clog << "path3_rules_node_ends.size(): " << path3_rules_node_ends.size() << endl;
                clog << "path3_rules_edges.size(): " << path3_rules_edges.size() << endl;

                VI vc;
                {
                    VVI W(N);
                    for (auto [a,b] : path3_rules_edges) GraphUtils::addEdge(W,a,b);
                    NuMVC numvc;
                    auto mis = numvc.solve(W, 7 ); // 3sec
                    vc = CombinatoricUtils::getFullSetDifference(W.size(), mis);
                    clog << endl << "VC of graph W: " << vc.size() << endl;
                }

                VVI sets;
                for ( int i=0; i<N; i++ ) if ( !hit[i] && !V[i].empty() ) {
                    sets.push_back(V[i]);
                    sets.back().push_back(i);
                }
                HSLS::fillByHSToValidHS(sets,vc);
                assert(isCorrect(V,vc,K,hit));
                clog << "After filling to valid HS, vc.size(): " << vc.size() << endl;

                {
                    VB res = StandardUtils::toVB(N,vc);
                    LiftableRule::liftSolution(liftable_rules,res,true);
                    VI S = StandardUtils::toVI(res);
                    clog << "After lifting rules, S.size(): " << S.size() << endl;
                    assert(isCorrect(V0, S,K, hit_nodes_0));
                }
            }

            exit(4);
        }

        if constexpr (enable_logs) {
            int hit_count = accumulate(ALL(hit), 0);
            DEBUG(hit_count);
        }
        M = GraphUtils::countEdges(V);
        if constexpr (enable_logs) DEBUG(M);

        VI isolated_nodes, nonisolated_nodes;
        for(int i=0; i<N; i++) {
            if( V[i].empty() ) isolated_nodes.push_back(i);
            else nonisolated_nodes.push_back(i);
        }
        auto gg = GraphInducer::induce(V, nonisolated_nodes);
        swap(g2,gg);
        V = g2.V;
        N = V.size();
        M = GraphUtils::countEdges(V);

        if (N > 0) {
            VB hit2(N), excluded2(N);
            for( int i=0; i<hit.size(); i++ ) if(hit[i] && g2.perm.contains(i)) hit2[g2.perm[i]] = true;
            for( int i=0; i<excluded.size(); i++ ) if(excluded[i] && g2.perm.contains(i)) excluded2[g2.perm[i]] = true;
            swap(hit,hit2);
            swap(excluded,excluded2);

            VI penud2(N);
            // for( int i=0; i<penud.size(); i++ ) if(g2.perm.contains(i)) penud2[g2.perm[i]] = penud[i];
            // for( int i=0; i<penud.size(); i++ ) if(g2.perm.contains(i)) penud2[g2.perm[i]] = g2.perm[penud[i]]; // #TEST
            for( int i=0; i<N; i++ ) {
                int w = penud[g2.nodes[i]];
                if ( g2.perm.contains(w) ) penud2[i] = g2.perm[w];
                else penud2[i] = i;
            }
            swap(penud, penud2);
        }

        if constexpr (enable_logs) {
            int hit_count = accumulate(ALL(hit), 0);
            int excluded_count = accumulate(ALL(excluded), 0);
            DEBUG(hit_count); DEBUG(excluded_count);
        }

        if constexpr (enable_logs) {
            int hit_count = accumulate(ALL(hit_nodes), 0);
            int excluded_count = accumulate(ALL(excluded_nodes), 0);
            DEBUG(hit_count);  DEBUG(excluded_count);
            clog << "After preprocessing, N: " << N << ", M: " << M <<
                ", hit nodes: " << hit_count << ", excluded nodes: " << excluded_count << endl;
        }

        if constexpr (enable_logs) clog << "N: " << N << ", M: " << M << ", K: " << K << endl;
        if constexpr (enable_logs)
        if(!V.empty()) {
            GraphUtils::writeBasicGraphStatistics(V);

            int hit_deg2_nodes = 0;
            for(int i=0; i<N; i++) hit_deg2_nodes += (V[i].size() == 2) && hit_nodes[i];
            DEBUG(hit_deg2_nodes);

            int nodes_incident_to_only_deg2_nodes = 0;
            int deg2_nodes_incident_to_only_deg2_nodes = 0;
            int unhit_nodes_incident_to_only_unhit_deg2_nodes = 0;
            for(int i=0; i<N; i++) if(!V[i].empty()) {
                bool b = true, c = true;
                for(int d : V[i]) {
                    b &= ( V[d].size() == 2 );
                    c &= ( V[d].size() == 2 ) && !hit_nodes[d];
                }
                nodes_incident_to_only_deg2_nodes += b;
                deg2_nodes_incident_to_only_deg2_nodes += ( b && ( V[i].size() == 2 ) );
                unhit_nodes_incident_to_only_unhit_deg2_nodes += ( c && !hit_nodes[i] );
            }
            DEBUG(nodes_incident_to_only_deg2_nodes);
            DEBUG(unhit_nodes_incident_to_only_unhit_deg2_nodes);
            DEBUG(deg2_nodes_incident_to_only_deg2_nodes);
        }

        sw.stop("preprocessing");
        if constexpr (enable_logs)
            clog << "Preprocessing took " << sw.getTime("preprocessing") / 1000 << " seconds" << endl << endl;
        finished_preprocessing_in_time_limit = (reductions_limit_millis > sw.getTime("preprocessing"));
    }

    // constexpr bool solve_by_cpsat = true;
    int ML0 = sw.getLimit("main") - sw.getTime("main");
    // const bool solve_by_cpsat = (!recurse_on_disconnected && V.size() >= 500 && V.size() <= 50'000 && ML0 >= 2000 );

    bool cpsat_cond = false;
    constexpr bool admit_using_cpsat = false; // version 1 - use cpsat
    if constexpr (admit_using_cpsat){
        VVI comps = ConnectedComponents::getConnectedComponents(V);
        // cpsat_cond = (V.size() <= 30'000 && ML0 >= 10'000 // only if we have more than 2sec. we use CPSAT
        cpsat_cond = (GraphUtils::countEdges(V) <= 1'000'000 && ML0 >= 10'000 // only if we have more than 2sec. we use CPSAT
            &&
            (!recurse_on_disconnected ||
                comps.size() == 1));
                // (comps.size() == 1 && (finished_preprocessing_in_time_limit || liftable_rules.empty())) ) );

        cpsat_cond |= hs_track;
    }

    const bool solve_by_cpsat = (cpsat_cond && admit_using_cpsat);

    constexpr bool finish_after_preprocessing = false;
    if constexpr (finish_after_preprocessing) exit(8);


    VI res;
    // iota(ALL(res), 0);

    if( N > 0 ){ // here we find results
        bool use_locality_remapping = (false && !V.empty() && V.size() <= 100'000 && !recurse_on_disconnected);
        VVI W;
        VI mapper, order;
        VB hn(N), en(N);
        if (use_locality_remapping) {
            sw.start("remapping");
            order = GraphRemapper::createRemappingNodeOrder(V);
            tie(W,mapper) = GraphRemapper::remapGraph(V,order);
            sw.stop("remapping");
            if constexpr (enable_logs)
                clog << "Remapping graph took " << sw.getTime("remapping") / 1000 << " sec." << endl;
            swap(V,W);

            {
                VB was(N);
                int cnt = 0;
                for( int d : mapper ) {
                    cnt += !was[d];
                    was[d] = true;
                }
                assert(cnt == N);
            }

            for( int i=0; i<N; i++ ) {
                hn[i] = hit_nodes[order[i]];
                en[i] = excluded_nodes[order[i]];
            }
            swap(hn, hit_nodes);
            swap(en, excluded_nodes);
        }

        // this will only be used if there are > 1 conn.comps.
        const bool use_hill_climber_at_the_end = (true && K == 1 ); // original
        // const bool use_hill_climber_at_the_end = (true && K == 1 && recursion_level < MAX_RECURSION_LEVEL ); // #TEST

        if(solve_by_cpsat) {
            // res = VI(N); iota(ALL(res),0);
            VVI __sets; __sets.reserve(N);
            for( int i=0; i<N; i++ ) if(!hit_nodes[i]) {
                __sets.push_back(V[i]);
                __sets.back().push_back(i);
                REMCVAL(excluded_nodes,__sets.back());
                if(__sets.back().empty()) __sets.pop_back();
            }
            // HSLS::trimHsToNodesInSets(__sets,res);
            // assert(HSLS::isCorrectHS(__sets,res));

            {
                VI  remapper(N,-1);
                {
                    VI mapper(N,-1);
                    set<int> zb;
                    for(auto & v : __sets) zb.insert(ALL(v));
                    int cnt = 0;
                    for(int d : zb) { mapper[d] = cnt; remapper[cnt] = d; cnt++; }
                    for( auto & v : __sets ) for(int & d : v) d = mapper[d];
                }

                DSSE dsse(V, hit_nodes, excluded_nodes);
                int millis_left = sw.getLimit("main") - sw.getTime("main");
                // millis_left *= 0.33;
                millis_left *= 0.3;
                clog << "Solving using CPSAT for " << millis_left / 1000 << " seconds" << endl;
                dsse.exact_hs_solving_method = CPSAT;
                // res = dsse.findMHSForSets(__sets, CPSAT, millis_left);
                res = dsse.findMHSForSetsCPSAT(__sets, millis_left, true);
                if (!isCorrect(V,res,K,hit_nodes) ) HSLS::fillByHSToValidHS(__sets, res);

                for (int & d : res) d = remapper[d];
                for( auto & v : __sets ) for(int & d : v) d = remapper[d];

                DEBUG(res.size());
                // return res;
            }

            VVI sets_always_hit;
            tie(res,sets_always_hit) = HSLS::hsImprovementLS(__sets, res, hit_nodes, sw,
                // 250 * __sets.size(), 1,false,false,false);
                50 * __sets.size(), 1,false,false,false);

            auto res2 = baselineHG(V, K, res);
            if (res2.size() < res.size()) swap(res,res2);

            assert( isCorrect(V,res,K,hit_nodes) );
        }else
        {
            if(recurse_on_disconnected){
                auto comps = ConnectedComponents::getConnectedComponents(V);
                if( comps.size() == 1 && (finished_preprocessing_in_time_limit || liftable_rules.empty()) ) {
                    res = baselineHG(V,K);
                }
                else {
                    if constexpr (enable_logs)
                        clog << "After preprocessing graph is disconnected, running recursively with limited time" << endl;
                    int time_left = sw.getLimit("main") - sw.getTime("main");
                    VB was(N);

                    auto getCompSize = [&]( VI & cmp )->int {
                        int S = 0;
                        // S = cmp.size(); // use number of nodes

                        {
                            // using number of nodes + edges in the graph
                            int e = 0;
                            for(int d : cmp) was[d] = true;
                            for(int d : cmp) for(int dd : V[d]) e += was[dd];
                            for(int d : cmp) was[d] = false;
                            S = cmp.size() + e;
                        }

                        // selection of scaling
                        return S; // this seems ok
                        // return S * (1.0 + sqrt(S));
                        // return S * (1.0 + log(S));
                        // return S / (1.0 + log(S));
                    };
                    int total_size = 0;
                    for( auto & cmp : comps ) total_size += getCompSize(cmp);

                    sort(ALL(comps), [&]( auto & v1, auto & v2 ){ return v1.size() < v2.size(); });

                    // constexpr int MIN_SUBGRAPH_SIZE = 1'000; // #TEST - on some instanec better, on other worse...
                    // constexpr int MIN_SUBGRAPH_SIZE = 500; // process subgraphs containing many small conn.comps
                    constexpr int MIN_SUBGRAPH_SIZE = 200; // #TEST
                    int iter = 0;
                    VI cmp; cmp.reserve(N);

                    for( auto & cmp1 : comps ) {
                        cmp += cmp1;
                        iter++;
                        if( (cmp.size() < MIN_SUBGRAPH_SIZE) && (iter < comps.size()) ) continue;

                        // for( auto & cmp : comps ) {
                        assert( cmp.size() >= 2 ); // graph was induced by nonisolated nodes...

                        auto gg = GraphInducer::induce(V,cmp);
                        int n = gg.V.size();
                        VB h(n), e(n);
                        for( int i=0; i<n; i++ ) h[i] = hit_nodes[gg.nodes[i]];
                        for( int i=0; i<n; i++ ) e[i] = excluded_nodes[gg.nodes[i]];

                        constexpr bool update_time_left = true;
                        if constexpr (update_time_left) time_left = sw.getLimit("main") - sw.getTime("main");
                        constexpr double ADD = 15; // original 15 #TEST
                        constexpr double FACT = 1.0; // original 1.0

                        Stopwatch s;
                        DSS dss_rec(s,h,e);
                        dss_rec.exact_hs_solving_method = exact_hs_solving_method;
                        dss_rec.find_exact_result = find_exact_result;
                        dss_rec.recursion_level = recursion_level+1;
                        dss_rec.hs_track = hs_track;
                        // int time_for_cmp = 1 + 1.0 * time_left * getCompSize(cmp) / total_size;
                        int time_for_cmp = max(5.0, ADD + FACT * time_left * getCompSize(cmp) / total_size);
                        if constexpr (update_time_left) total_size -= getCompSize(cmp);
                        if (use_hill_climber_at_the_end) time_for_cmp *= 0.9; // original value 0.85, 0.9 works well too

                        // auto r = dss_rec.solveH(gg.V, K, false, time_for_cmp,
                        // leave_at_K1, false);

                        bool use_prepr_on_next_level = (use_multilevel_preprocessing && use_preprocessing && !finished_preprocessing_in_time_limit);
                        use_prepr_on_next_level &= !liftable_rules.empty();

                        {
                            VI penud_gg(n);
                            // for (int i=0; i<n; i++) penud_gg[i] = penud[gg.nodes[i]];
                            // for (int i=0; i<n; i++) penud_gg[i] = gg.perm[penud[gg.nodes[i]]]; // #TEST
                            for (int i=0; i<n; i++) {
                                int w = penud[gg.nodes[i]];
                                if ( gg.perm.contains(w) ) penud_gg[i] = gg.perm[w]; // #TEST
                                else penud_gg[i] = i;
                            }
                            dss_rec.permanent_excluded_node_unhit_dominator = penud_gg;
                        }

                        auto r = dss_rec.solveH(gg.V, K,
                            use_prepr_on_next_level,
                            time_for_cmp, leave_at_K1,
                            (dss_rec.recursion_level <= MAX_RECURSION_LEVEL) && !finished_preprocessing_in_time_limit
                            ); // do not recurse more and do not use preprocessing

                        gg.remapNodes(r);
                        res += r;


                        cmp.clear();
                    }
                    // assert(cmp.empty());

                    if(!isCorrect(V,res,K,hit_nodes)) {
                        writeUnhitNodes(V,res,K,hit_nodes);
                        assert(isCorrect(V,res,K,hit_nodes));
                    }
                }
            }
            else res = baselineHG(V,K);
        }

        // if (use_hill_climber_at_the_end) if( recursion_level == 0 && !sw.tle("main") ) {
        if(!find_exact_result)
        if (use_hill_climber_at_the_end) if( !sw.tle("main") ) {
            int millis_left = sw.getLimit("main") - sw.getTime("main");
            if constexpr (enable_logs)
                clog << endl << "--> Starting hill climber, time left: " << millis_left << " millis" << endl;
            res = hillClimberDS(V,res);
        }


        if (use_locality_remapping) {
            for( int & d : res ) d = order[d];
            swap(hn, hit_nodes);
            swap(en, excluded_nodes);
            swap(V,W);
        }
    }

    if constexpr (enable_logs) DEBUG(res.size());


    assert( isCorrect( V, res, K, hit_nodes ) );

    if constexpr (enable_logs) {
        ENDL(2); ENDLS(50, "*"); ENDL(2);
    }


    if( use_preprocessing ) {
        assert(isCorrect(g2.V, res, K, hit_nodes));

        auto writeAllRulesAffectingNode = [&](auto & rules, int v) {
              for ( auto r : rules ) {
                  if ( r->affectsNode(v) ) {
                      clog << "Rule affects node " << v << endl;
                      clog << "\t" << r->getDescription() << endl;
                  }
              }
        };

        g2.remapNodes(res);
        { // lifting reduction rules
            if constexpr (enable_logs) clog << endl << "Before lifting rules, res.size(): " << res.size() << endl;
            if constexpr (enable_logs) clog << "\tliftable_rules.size(): " << liftable_rules.size() << endl;
            VB res_mask = StandardUtils::toVB( initV.size(), res);
            reverse(ALL(liftable_rules));

            if constexpr (enable_logs) {
                ENDL(1);
                DEBUG(LiftableRule::getReductionsFrequencies(liftable_rules));
                ENDL(1);
            }

            // writeAllRulesAffectingNode(liftable_rules,724101);

            for( auto * dr : liftable_rules ) dr->lift(res_mask);
            for( auto * dr : liftable_rules ) delete dr;
            liftable_rules.clear();

            res = StandardUtils::toVI(res_mask);
            if constexpr (enable_logs) clog << "After lifting rules, res.size(): " << res.size() << endl;
        }

        bool is_correct = isCorrect(g.V, res, K, hit_nodes_1);
        if constexpr (enable_logs) DEBUG(is_correct);

        if(!is_correct) {
            if (K == 1){
                DEBUG(V0.size());
                DEBUG(GraphUtils::countEdges(V0));
                // cout << "c incorrect solution after lifting..." << endl;
                // cout << "c thread id: " << omp_get_thread_num() << endl;

                VB was(g.V.size());
                for (int d : res) was[d] = true;
                int nodes_unhit = 0;
                VB res_mask =  StandardUtils::toVB(g.V.size(), res);

                for ( int i=0; i<g.V.size(); i++ ) if(!hit_nodes_1[i]) {
                    bool h = was[i];
                    for (int d : g.V[i]) h |= was[d];
                    nodes_unhit += !h;
                    if (!h) {
                        clog << "Node " << i << " is unhit! N[" << i << "]: " << g.V[i] << endl;
                        for (int d : g.V[i]){ clog << "\t"; DEBUGV(g.V,d); }
                        clog << "Node " << i << " is unhit!" << endl;

                        auto WR = [&](int i) {
                            DEBUGV(g.V,i);
                            DEBUG(g2.perm.contains(i));
                            if (g2.perm.contains(i)) {
                                DEBUGV(g2.perm,i);
                                DEBUGV(g2.V, g2.perm[i]);
                                clog << "is_in_ds_in_g[" << i << "]: " << res_mask[i] << endl;
                                clog << "excluded _in_g2[" << i << "]: " << excluded[g2.perm[i]] << endl;
                                clog << "hit_ib_g2[" << i << "]: " << hit[g2.perm[i]] << endl;
                            }
                            clog << endl;
                        };
                        WR(i);
                        for (int d : g.V[i]) WR(d);
                    }

                }
                DEBUG(nodes_unhit);
            }

            ofstream str("reduction_lift_fail_graph.txt");
            // auto edges = GraphUtils::getGraphEdges(g.V);
            auto edges = GraphUtils::getGraphEdges(initV);
            int M = edges.size();
            str << initV.size() << " " << M << endl;
            for(auto [a,b] : edges) str << a << " " << b << "\n";
            str << K << endl;
            str.close();

            ENDL(2);
            clog << "Hints:" << endl;
            clog << "Test whether disabling excluded nodes feature in preprocessing fixes the issue" << endl;
            clog << "Test, whether fast versions of dom and dom3 reduction rules are correct" << endl;
            clog << "Test, whether parallel paths rule (paths3) is correct" << endl;
            clog << "Test whether excluded_and_hit nodes can be removed in preprocessing" << endl;
            clog << "Test whether 2nd and 3rd rules from basic_excluded_rule can be used" << endl;
            clog << "Test whether setting remove_additional_nodes_in_funnels_on_the_spot to false in DSReducer"
                    " solves the problem" << endl;

            assert(isCorrect(g.V, res, K, hit_nodes_1));
        }
    }

    // auto hn = ( recurse_on_disconnected ? VB(g.V.size()) : hit_nodes_1 );
    if constexpr (induce_by_nonisolated_nodes) {
        if(!isCorrect(g.V, res, K,hit_nodes_1)) {
            DEBUG(use_preprocessing);
            DEBUG(isolated_nodes.size());
            assert( isCorrect(g.V, res, K,hit_nodes_1) );
        }
        g.remapNodes(res);
        res += isolated_nodes;
        if constexpr (enable_logs) clog << endl << "\tAdding " << isolated_nodes.size() << " isolated nodes back to V" << endl;
        if constexpr (enable_logs)
            clog << "After adding isolated nodes from initial graph, res.size(): " << res.size() << endl;
        assert( isCorrect(V0,res,K,hit_nodes_0) );
    }

    V = V0;
    hit_nodes = hit_nodes_0;
    excluded_nodes = excluded_nodes_0;
    permanent_excluded_node_unhit_dominator = penud_0;
    N = V.size();
    assert( isCorrect(V,res,K,hit_nodes_0) );
    if constexpr (enable_logs) DEBUG(res.size());

    if constexpr (enable_logs) clog << res.size() << endl;
    // cout << res.size() << endl;
    // for(int d : res) cout << d << " ";  cout << endl;

    if constexpr (enable_logs) sw.writeAll();

    return res;
}


bool isCorrect(VVI V, VI S, int K) {
    int N = V.size();
    int inf = 1e9;
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

    int visited = 0;
    // for(int i=0; i<N; i++) if( dst[i] <= K ) visited++;
    // for(int i=0; i<N; i++) if( dst[i] <= K ) visited++;
    for(int i=0; i<N; i++) visited += ( dst[i] <= K ) ;
    // clog << "Visited: " << visited << endl;
    return visited == N;
}


bool DSS::isCorrect(VVI &V, VI S, int K) {
    int N = V.size();
    int inf = 1e9;
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

    int visited = 0;
    // for(int i=0; i<N; i++) if( dst[i] <= K ) visited++;
    // for(int i=0; i<N; i++) if( dst[i] <= K ) visited++;
    for(int i=0; i<N; i++) visited += ( dst[i] <= K ) ;
    // clog << "Visited: " << visited << endl;
    return visited == N;
}

bool DSS::isCorrect(VVI &V, VI S, int K, VB & hit_nodes) {
    if(K == 1) {
        VB was(V.size());
        for(int v : S) {
            was[v] = true;
            for(int d : V[v]) was[d] = true;
        }
        for(int i=0; i<V.size(); i++) if(!was[i] && !hit_nodes[i]) return false;
        return true;
    }

    int N = V.size();
    int inf = 1e9;
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

    int visited = 0;
    for(int i=0; i<N; i++) visited += ( (dst[i] <= K) || hit_nodes[i] );
    return visited == N;
}


tuple<VVI,VI,VI> HSLS::reduceForHSLSOld(VVI sets, VI hs) {
    VVI V;
    int N = 0;
    for(VI C : sets) for(int d : C) N = max(N,d+1);

    int S = sets.size();
    V = VVI(N); // V[i] is the list of ids of sets that contain node i

    for( int i=0; i<S; i++ ){
        for( int d : sets[i] ){
            V[d].push_back(i);
        }
    }
    VVI covered_by(S);
    VI kernel;

    // assert( HittingSetLS::isCorrectHS(sets, hs, hit_nodes) );

    VB was(N);

    for( int v : hs ) for( int d : V[v] ) covered_by[d].push_back(v);
    for( int i=(int)sets.size()-1; i>=0; i-- ) {
        // assert(!covered_by[i].empty());

        if( covered_by[i].size() <= 1 ) {
            if( covered_by[i].size() == 1 ) {
                for(int d : sets[i]) was[d] = true;

                int xx = covered_by[i][0];
                kernel.push_back(xx);
                for( int ii : V[xx] ) {
                    // auto it = find(ALL(covered_by[ii]),xx);
                    // assert(it != covered_by[ii].end());
                    // covered_by[ii].erase(it);
                    for( int j=(int)covered_by[ii].size()-1; j>=0; j-- ) {
                        if( covered_by[ii][j] == xx ) {
                            swap(covered_by[ii][j], covered_by[ii].back());
                            covered_by[ii].pop_back();
                            break;
                        }
                    }
                }

                for(int d : sets[i]) was[d] = false;
            }
            swap( sets[i], sets.back() );
            sets.pop_back();
        }
    }

    // assert( HittingSetLS::isCorrectHS(sets, hs, hit_nodes) );

    assert( none_of(ALL(was), [](auto a){return a;}) );
    // StandardUtils::makeUnique(kernel);
    for(int d : kernel) was[d] = true;
    // StandardUtils::removeFromArrayInplace(hs,kernel);
    for( int i = (int)hs.size()-1; i>=0; i-- ) {
        if( hs[i] < N && was[hs[i]] ) {
            swap(hs[i], hs.back());
            hs.pop_back();
        }
    }

    // assert( HittingSetLS::isCorrectHS(sets, hs+kernel, hit_nodes) );

    // IntGenerator rnd;
    if(false) {
        // #CAUTION #TEST - if this is used, then hs+kernel will not be a hitting set of returned sets...
    // if(rnd.nextInt(4) > 0) {
        for( int i=(int)sets.size()-1; i>=0; i-- ) { // #CAUTION - this is logically faulty...
            for( int j = (int)sets[i].size()-1; j>=0; j-- ) {
                if( was[sets[i][j]] ) {
                    swap(sets[i][j], sets[i].back());
                    sets[i].pop_back();
                }
            }
            if(sets[i].empty()) {
                swap(sets[i], sets.back());
                sets.pop_back();
            }
        }
    }
    else {
    // else if(false) { // do not remove sets that are hit...
        for( int i=(int)sets.size()-1; i>=0; i-- ) { // this is correct though...
            for( int j = (int)sets[i].size()-1; j>=0; j-- ) if( was[sets[i][j]] ) { REM(sets,i); break; }
            // for( int found = false, j = (int)sets[i].size()-1; j>=0; j-- ) {
            //     if( was[sets[i][j]] ) found = true;
            //     if( found && !was[sets[i][j]] ) { REM(sets,i); break; }
            // }
            if(i < sets.size() && sets[i].empty()) REM(sets,i);
        }
        HittingSetLS::trimHsToNodesInSets(sets,hs);
    }

    // assert(kernel.size() == set(ALL(kernel)).size());
    assert( HittingSetLS::isCorrectHS(sets, hs+kernel, hit_nodes) );

    if( kernel.empty() )
        return { sets, hs, kernel };

    auto [sets2, hs2, kern2] = reduceForHSLSOld( sets, hs );
    // DEBUG(kernel.size());
    // DEBUG(kernel);
    // DEBUG(kern2.size());
    // DEBUG(kernel.size() + kern2.size());
    return { sets2, hs2, kern2 + kernel };
}

tuple<VVI,VI,VI> HSLS::reduceForHSLS(VVI sets, VI hs) {
    IntGenerator rnd;
    if( rnd.nextInt(10) > 0 ) return reduceForHSLSOld(sets, hs); // #TEST

    if( sets.empty() || hs.empty() ) return {sets, hs, {}};

    VI kernel;
    tie(sets,hs,kernel) = simplePreprocess(sets,hs);

    if( sets.empty() ) return {sets, hs, kernel};


    // N = 0;
    int N = *max_element(ALL(hs))+1;
    if(!kernel.empty()) N = max(N,*max_element(ALL(kernel))+1);
    for(VI C : sets) for(int d : C) N = max(N,d+1);
    int S = sets.size();

    // fill(ALL(was),false);
    VB was(N);

    VVI V = VVI(N); // V[i] is the list of ids of sets that contain node i
    for( int i=0; i<S; i++ ){
        for( int d : sets[i] ){
            V[d].push_back(i);
        }
    }

    S = sets.size();
    VVI covered_by(S);
    for( int v : hs ) for( int d : V[v] ) covered_by[d].push_back(v);
    for( int i=(int)sets.size()-1; i>=0; i-- ) {
        // assert(!covered_by[i].empty());

        if( covered_by[i].size() <= 1 ) {
            if( covered_by[i].size() == 1 ) {
                for(int d : sets[i]) was[d] = true;

                int xx = covered_by[i][0];
                kernel.push_back(xx);
                for( int ii : V[xx] ) {
                    // auto it = find(ALL(covered_by[ii]),xx);
                    // assert(it != covered_by[ii].end());
                    // covered_by[ii].erase(it);
                    for( int j=(int)covered_by[ii].size()-1; j>=0; j-- ) {
                        if( covered_by[ii][j] == xx ) {
                            swap(covered_by[ii][j], covered_by[ii].back());
                            covered_by[ii].pop_back();
                            break;
                        }
                    }
                }

                for(int d : sets[i]) was[d] = false;
            }
            swap( sets[i], sets.back() );
            sets.pop_back();
        }
    }

    // StandardUtils::makeUnique(kernel);
    for(int d : kernel) was[d] = true;
    // StandardUtils::removeFromArrayInplace(hs,kernel);
    for( int i = (int)hs.size()-1; i>=0; i-- ) {
        if( hs[i] < N && was[hs[i]] ) {
            swap(hs[i], hs.back());
            hs.pop_back();
        }
    }

    if(true) {
        for( int i=(int)sets.size()-1; i>=0; i-- ) {
            for( int j = (int)sets[i].size()-1; j>=0; j-- ) {
                if( was[sets[i][j]] ) {
                    REM(sets,i);
                    break;
                }
            }
            if(i < sets.size() && sets[i].empty()) {
                swap(sets[i], sets.back());
                sets.pop_back();
            }
        }
    }
    else {
        // #CAUTION #TEST - if this is used, then hs+kernel will not be a hitting set of returned sets...
        for( int i=(int)sets.size()-1; i>=0; i-- ) {
            for( int j = (sets[i].size()-1); j>=0; j-- ) if( was[sets[i][j]] ) REM(sets[i],j);
            if(sets[i].empty()) REM(sets,i);
        }
    }

    if(kernel.size() != set(ALL(kernel)).size()) {
        ranges::sort(kernel);
        DEBUG(kernel);
        for( int i=1; i<kernel.size(); i++ ) if( kernel[i] == kernel[i-1] ) {
            clog << "element " << kernel[i] << " occurs more than once in kernel" << endl;
        }
        clog << "sets: " << endl;
        for(auto & v : sets) DEBUG(v);
        assert(kernel.size() == set(ALL(kernel)).size());
    }

    if(!hs.empty()) HittingSetLS::trimHsToNodesInSets(sets,hs);

    // if( kernel.empty() )
        // return { sets, hs, kernel };
    if( kernel.empty() || sets.empty() )
        return { sets, hs, kernel };

    assert(HittingSetLS::isCorrectHS(sets, hs+kernel, hit_nodes));

    auto [sets2, hs2, kern2] = reduceForHSLS( sets, hs );
    // auto [sets2, hs2, kern2] = reduceForHSLSOld( sets, hs ); // #TEST
    // DEBUG(kernel.size());
    // DEBUG(kernel);
    // DEBUG(kern2.size());
    // DEBUG(kernel.size() + kern2.size());
    return { sets2, hs2, kern2 + kernel };
}


void DominatingSetSolver::writeUnhitNodes(VVI V, VI res, int K, VB hit_nodes) {
    if (K == 1){

        VB was(V.size());
        for (int d : res) was[d] = true;
        int nodes_unhit = 0;
        VB res_mask =  StandardUtils::toVB(V.size(), res);

        for ( int i=0; i<V.size(); i++ ) if(!hit_nodes[i]) {
            bool h = was[i];
            for (int d : V[i]) h |= was[d];
            nodes_unhit += !h;
            if (!h) {
                clog << "Node " << i << " is unhit! N[" << i << "]: " << V[i] << endl;
                for (int d : V[i]){ clog << "\t"; DEBUGV(V,d); }
                clog << "Node " << i << " is unhit!" << endl;
                DEBUGV(V,i);
            }
        }
        DEBUG(nodes_unhit);
    }
}

VI DominatingSetSolver::findDSOfHSGraph(VVI& V, int time_limit_millis) {
    int N = V.size();

    VVI __sets; __sets.reserve(N);
    for( int i=0; i<N; i++ ) if(!hit_nodes[i]) {
        __sets.push_back(V[i]);
        __sets.back().push_back(i);
        REMCVAL(excluded_nodes,__sets.back());
        if(__sets.back().empty()) __sets.pop_back();
    }

    set<int> zb;
    for (auto & s : __sets) zb.insert(ALL(s));
    VI mapper(N,-1), remapper(N,-1);
    int cnt = 0;
    for (int v : zb) {
        mapper[v] = cnt;
        remapper[cnt] = v;
        cnt++;
    }

    for ( auto & s : __sets ) for (int & d : s) d = mapper[d];

    set<PII> edges;

    // for ( auto & s : __sets ) { // for vertex cover / almost vertex cover
    //     for ( int i=0; i<s.size(); i++ ) {
    //         for (int j=i+1; j<s.size(); j++) {
    //             int a = s[i], b = s[j];
    //             if (a>b) swap(a,b);
    //             edges.insert(PII(a,b));
    //         }
    //     }
    // }

    // for ( auto & s : __sets ) {
    //     int v = *min_element(ALL(s));
    //     for ( int u : s ) if ( u != v ) edges.insert( {min(u,v), max(u,v)} );
    // }

    // for ( auto s : __sets ) { // for feedback vertex set
    //     sort(ALL(s));
    //     s.push_back(s[0]);
    //     for ( int i=1; i<s.size(); i++ ) {
    //         int u = s[i-1], v = s[i];
    //         if (u>v) swap(u,v);
    //         edges.insert( {u,v} );
    //     }
    // }

    VI freq(N,0);
    for (auto & s : __sets) for (int d : s) freq[d]++;

    for ( auto s : __sets ) { // for directed feedback vertex set
        auto cmp1 = [&](int a, int b) {
            if (V[a].size() != V[b].size()) return V[a].size() < V[b].size();
            return a < b;
        };

        auto cmp2 = [&](int a, int b) {
            if (freq[a] != freq[b]) return freq[a] < freq[b];
            if (V[a].size() != V[b].size()) return V[a].size() < V[b].size();
            return a < b;
        };

        auto cmp3 = [&](int a, int b) {
            if (freq[a] != freq[b]) return freq[a] > freq[b];
            if (V[a].size() != V[b].size()) return V[a].size() < V[b].size();
            return a < b;
        };

        sort(ALL(s), cmp1);
        s.push_back(s[0]);
        for ( int i=1; i<s.size(); i++ ) {
            int u = s[i-1], v = s[i];
            if (u>v) swap(u,v);
            edges.insert( {u,v} );
        }
    }

    VVI W(cnt);
    for (auto [a,b] : edges) GraphUtils::addEdge(W,a,b);

    clog << "Created graph W of size " << cnt << " and " << GraphUtils::countEdges(W) << " edges" << endl;
    VI res;

    {
        Stopwatch timer;
        timer.setLimit("main", time_limit_millis);
        timer.start("main");
        DSS dss(timer);
        dss.recursion_level = 100;
        res = dss.solveH(W,1,true,time_limit_millis,true,false);
        timer.stop("main");
        clog << endl << "DS of graph W: " << res.size() << endl;
    }

    clog << "Created graph W of size " << cnt << " and " << GraphUtils::countEdges(W) << " edges" << endl;

    {
        NuMVC numvc;
        auto mis = numvc.solve(W, time_limit_millis / 1000.0 );
        res = CombinatoricUtils::getFullSetDifference(W.size(), mis);
        clog << endl << "VC of graph W: " << res.size() << endl;
    }



    for ( auto & d : res ) d = remapper[d];
    return res;
}

VI DSS::baseline1(VVI V, int K, VI initS) {
    int N = V.size();

    // VI perm(N);
    // iota(ALL(perm),0);
    VI perm = initS;
    if(perm.empty()) {
        perm.resize(N);
        iota(ALL(perm),0);
    }


    auto findResForPerm = [&]() {
        if(sw.tle()) return perm;

        VI S;
        VI dst(N,inf);
        VB was(N);

        VB covered(N);

        for(int i =0; i<perm.size(); i++) {
            if( (i & 255) == 0) if( sw.tle() ) break;
            int v = perm[i];

            if( !covered[v] ) {
                S.push_back(v);
                auto reachables = findReachableNodesFromSWithinDistanceK(V,S,K, dst, was);
                for(int d : reachables) covered[d] = true;
            }
        }

        if(!isCorrect(V,S,K)) {
            S += findFurthestUnreachableNodes(V,S,K,hit_nodes, 1e9);
        }

        return S;
    };

    // auto res = findResForPerm();
    //
    // auto cmp = [&](int a, int b){ return V[a].size() > V[b].size(); };
    // sort(ALL(perm), cmp);
    // auto res2 = findResForPerm();
    // if( res2.size() < res.size() ) res = res2;
    //
    // reverse(ALL(perm));
    // auto res3 = findResForPerm();
    // if( res3.size() < res.size() ) res = res3;


    auto cmp = [&](int a, int b){ return V[a].size() > V[b].size(); };
    sort(ALL(perm), cmp);
    auto res = findResForPerm();


    assert(isCorrect(V,res,K));

    return res;
}


VI DSS::baseline1v2(VVI V, int K) {
    int N = V.size();


    VI S;
    VI deg1(N,0);

    auto cmp = [&]( int a, int b ) {
        if( deg1[a] != deg1[b] ) return deg1[a] > deg1[b];
        if(V[a].size() != V[b].size()) return V[a].size() > V[b].size();
        return a < b;
    };

    VB inS(N);
    VB covered(N);
    VI dst(N,inf);
    VB was(N);

    while( !isCorrect(V,S,K) ) {
        if(sw.tle()) break;
        fill(ALL(deg1),0);

        for( int i=0; i<N; i++ ) if(!covered[i] ) {
            if(sw.tle()) break;

            int cnt = 0;
            for( int d : V[i] ) if(!covered[d]) cnt++;
            if(cnt == 1) {
                auto reachables = findReachableNodesFromSWithinDistanceK(V,{i},K,dst,was);
                for( int d : reachables ) if( !covered[d] ) deg1[d]++;
            }
        }

        int v = -1;
        for(int i=0; i<N; i++) if( !covered[i] ) if( v == -1 || cmp( i,v ) ) v = i;
        assert(v != -1);

        S.push_back(v);
        auto reachables = findReachableNodesFromSWithinDistanceK(V,{v},K,dst,was);
        for(int d : reachables) covered[d] = true;
    }

    if(!isCorrect(V,S,K)) {
        S += findFurthestUnreachableNodes(V,S,K,hit_nodes, inf);
    }

    assert(isCorrect(V,S,K));

    return S;
}


VI DSS::baseline2(VVI V, int K) {
    int N = V.size();
    if(N == 0) return {};
    // if( K == 1 && N >= 50'000 ) return baseline1(V,K,15); // return just a vc for dominating set

    VI degk(N,0);
    VI dst(N,inf);
    VB was(N);

    // for( int i=0; i<N; i++ ) degk[i] = findReachableNodesFromSWithinDistanceK(V,{i},K, dst,was).size();
    for( int i=0; i<N; i++ ) {
        if( (i&255) == 0 && sw.tle() ) return VI(N);
        degk[i] = findReachableNodesFromSWithinDistanceK(V,{i},min(K,3), dst,was).size();
    }


    auto & deg_tab = degk;
    // auto & deg_tab = degn2;

    VB in_cur_res(N);
    VI cur_res;
    for(int i=0; i<N; i++) if(V[i].empty()) cur_res.push_back(i);
    for(int d : cur_res) in_cur_res[d] = true;

    VI dst_from_beg(N,inf);
    VB is_boundary_node(N,false);
    VI bnd_nodes_covered(N,0);
    VI bnd_nodes_covered_cnt(N,0);

    {
        int beg = N/2;
        VI neigh = {beg};
        VB was(N);
        was[beg] = true;
        dst_from_beg[beg] = 0;
        for(int i=0; i<neigh.size(); i++) {
            int v = neigh[i];
            for( int d : V[v] ) if(!was[d]) {
                was[d] = true;
                neigh.push_back(d);
                dst_from_beg[d] = dst_from_beg[v] + 1;
            }
        }
    }


    auto cmp = [&](int a, int b) {
        if( deg_tab[a] != deg_tab[b] ) return deg_tab[a] > deg_tab[b];
        if( V[a].size() != V[b].size() ) return V[a].size() > V[b].size();
        if( bnd_nodes_covered[a] != bnd_nodes_covered[b] ) return bnd_nodes_covered[a] > bnd_nodes_covered[b];
        if( dst_from_beg[a] != dst_from_beg[b] ) return dst_from_beg[a] < dst_from_beg[b];
        return a < b;
    };
    set<int, decltype(cmp)> zb(cmp);
    for( int i=0; i<N; i++ ) if(!in_cur_res[i]) zb.insert(i);

    VB covered = in_cur_res;
    auto reachables = findReachableNodesFromSWithinDistanceK(V,cur_res,K);
    for(int d : reachables) covered[d] = true;

    VI reach;
    VI reach_cnt(N,0);

    VI bnd_nodes;
    VB was2(N);

    while( !zb.empty() ) {
        int v = *zb.begin();
        zb.erase(v);
        // if( in_cur_res[v] ) continue;
        // if( in_cur_res[v] && !covered[v] ) continue;
        if( in_cur_res[v] || covered[v] ) continue;
        // if( in_cur_res[v] || deg_tab[v] <= 0 ) continue;


        if( sw.tle() ) break;

        cur_res.push_back(v);
        in_cur_res[v] = true;
        covered[v] = true;

        reachables = findReachableNodesFromSWithinDistanceK(V,{v},K, dst,was);

        // for( int d : reachables ) covered[d] = true;
        reach.clear();

        for( int d : reachables ) {
            if(covered[d]) continue;
            if( sw.tle() ) break;


            auto neigh = findReachableNodesFromSWithinDistanceK(V,{d},K, dst,was);
            // for(int dd : neigh) if(!was[dd]) {
            for(int dd : neigh) if(!was[dd] && !covered[dd]) {
                was[dd] = true;
                reach.push_back(dd);
            }

            // reach += temp;
            for(int x : neigh) reach_cnt[x]++;
            for(int x : neigh) bnd_nodes_covered_cnt[x] += is_boundary_node[d];
        }

        for( int d : reach ) {
            was[d] = false;
            if(!covered[d]) {
                zb.erase(d);
                // deg_tab[d]--;
                deg_tab[d] -= reach_cnt[d];
                bnd_nodes_covered[d] -= bnd_nodes_covered_cnt[d];
                // if( !in_cur_res[d] && d != v ) zb.insert(d);
                if(!in_cur_res[d] && !covered[d]) zb.insert(d);
            }

            reach_cnt[d] = 0;
            bnd_nodes_covered_cnt[d] = 0;
        }


        for( int d : reachables ) covered[d] = true;

        if(false){
            bnd_nodes.clear();
            for( int d : reachables ) {
                for( int dd : V[d]) if( !covered[dd] && !was2[dd] && !is_boundary_node[dd] ) {
                    was2[dd] = true;
                    bnd_nodes.push_back(dd);
                }
            }
            for( int d : reach ) was2[d] = false;
            reach.clear();
            for( int d : bnd_nodes ) {
                auto neigh = findReachableNodesFromSWithinDistanceK(V,{d},K, dst,was);
                for(int dd : neigh) if(!was2[dd] && !covered[dd]) {
                    was2[dd] = true;
                    reach.push_back(dd);
                }
                for(int x : neigh) bnd_nodes_covered_cnt[x]++;
            }
            for( int d : reach ) was2[d] = false;
            for( int d : reach ) {
                if(!covered[d]) {
                    zb.erase(d);
                    bnd_nodes_covered[d] += bnd_nodes_covered_cnt[d];
                    zb.insert(d);
                }

                bnd_nodes_covered_cnt[d] = 0;
            }
        }
        if constexpr (enable_logs)
        if(cur_res.size() % 1'000 == 0) clog << "\rcur_res.size(): " << cur_res.size() << flush;
    }

    if(!isCorrect(V,cur_res,K)) {
        cur_res += findFurthestUnreachableNodes(V,cur_res,K,hit_nodes, inf);
    }

    assert(isCorrect(V,cur_res,K));

    if constexpr (enable_logs) DEBUG(cur_res.size());

    return cur_res;
}

VI DSS::baselineHG2(VVI V, int K) {
    int N = V.size();
    VVI sets;
    sets.reserve(N);

    VI S;
    VB was(N);
    VI dst(N,inf);
    if constexpr (enable_logs) clog << "Creating all constraints" << endl;
    for(int v=0; v<N; v++) {
        if(hit_nodes[v]) continue;
        auto reachables = findReachableNodesFromSWithinDistanceK(V,{v},K, dst,was);
        sets.push_back(reachables);
        S.push_back(v);
    }

    int total_elements_in_sets = accumulate(ALL(sets),0, [&](int s, auto & v){ return s + v.size(); });
    if constexpr (enable_logs) clog << "Starting to solve, there are " << sets.size()
         << " sets to hit and S.size(): " << S.size() << ", total_elements_in_sets: " << total_elements_in_sets
         << ", time: " << sw.getTime() / 1000 << endl;

    VVI sets_always_hit;
    tie(S,sets_always_hit) = HSLS::hsImprovementLS(sets, S, hit_nodes, sw, 1e8,1,false);
    if constexpr (enable_logs) DEBUG(S.size());

    assert(isCorrect(V,S,K));
    return S;
}

VI DSS::hillClimberDS(VVI &V, VI res) {

    int N = V.size();
    VVI sets; sets.reserve(N);
    for( int i=0; i<N; i++ ) if( !hit_nodes[i] ) {
        sets.push_back(V[i]);
        sets.back().push_back(i);
    }

    VVI sets_always_hit;

    bool tabu = true;
    while(!sw.tle("main")) {
        res = ds21swaps(V, res, 1, 10,false);
        int iters = 3*sets.size();
        if(hs_track) iters = 30 * sets.size();
        tie(res,sets_always_hit) = HSLS::hsImprovementLS(sets,res,hit_nodes,sw,iters,
            1,false,tabu = !tabu, false);
        // DEBUG(res.size());
    }


    return res;
}

VI DSS::baselineHG(VVI V, int K, VI initS) {
    if( V.empty() ) return {};
    if(sw.tle()) {
        DSS::fillGreedilyToValidSolution(V,initS, K, hit_nodes);
        initS = ds21swaps(V,initS,1,2,false);
        return initS;
    }

    VVI sets_always_hit;

    constexpr bool exclude_additional_nodes_at_start = true;
    if(exclude_additional_nodes_at_start){
        int cnt_before = 0;
        for(int i=0; i<V.size(); i++) cnt_before += excluded_nodes[i];
        DSReducer::markAdditionalExcludedNodes(V,hit_nodes, excluded_nodes);
        int cnt_after = 0;
        for(int i=0; i<V.size(); i++) cnt_after += excluded_nodes[i];
        if constexpr (enable_logs) clog << "There were " << cnt_after - cnt_before
             << " nodes additionally marked as excluded in baselineHG" << endl;

        int excluded_edges_removed = 0;
        for ( int i=0; i<V.size(); i++ ) if ( excluded_nodes[i] ) {
            int before = V[i].size();
            REMCVAL(excluded_nodes, V[i]);
            int after = V[i].size();
            excluded_edges_removed += before - after;
        }
        excluded_edges_removed >>= 1;
        if constexpr (enable_logs)
            clog << "There were " << excluded_edges_removed << " additionally removed edges" << endl;
    }

    constexpr bool use_only_full_hsls = false;

    VI res,S, fallback_res;
    VVI res_sets;
    int res_iters = -1;

    constexpr bool consider_vc_case = true;
    bool is_vc_case = false;
    if(K == 1 && consider_vc_case){
        is_vc_case = isVCCase(V,hit_nodes);
        if constexpr (enable_logs) DEBUG(is_vc_case);
        if(is_vc_case) {
            if constexpr (enable_logs) clog << "VC CASE" << endl;
            auto [W,mapper,remapper] = transformToVC(V, hit_nodes);
            if constexpr (enable_logs) clog << "Transformed graph has " << W.size() << " nodes and "
                 << GraphUtils::countEdges(W) << " edges" << endl;
            double time_left_sec = 0.4 * (sw.getLimit("main") - sw.getTime("main")) / 1000;
            IntGenerator rnd;
            int seed = rnd.nextInt(1e9);
            VI mis, vc;

            { // fastvc
                VPII edges = GraphUtils::getGraphEdges(W);
                VI init_vc;
                libmvc::FastVC fastvc(edges, W.size(), 0,
                    std::chrono::milliseconds(int(1000 * time_left_sec)), false, seed, init_vc);
                if constexpr (enable_logs) clog << "Starting FastVC, running for " << time_left_sec << " seconds" << endl;
                fastvc.cover_LS();
                mis = fastvc.get_independent_set(false);
                vc = CombinatoricUtils::getFullSetDifference(W.size(), mis);
                assert(VCUtils::isVertexCover(W,vc));
                if constexpr (enable_logs) clog << "vc found by FastVC: " << vc.size() << endl;
            }

            { // numvc
                if constexpr (enable_logs) clog << "Starting NuMVC, running for " << time_left_sec << " seconds" << endl;
                NuMVC numvc;
                mis = numvc.solve( W, time_left_sec, vc, 1, seed );
                vc = CombinatoricUtils::getFullSetDifference(W.size(), mis);
                assert(VCUtils::isVertexCover(W,vc));
                if constexpr (enable_logs) clog << "vc found by NuMVC, initialized with vc produced by FastVC: " << vc.size() << endl;
            }

            for(int & d : vc) d = remapper[d]; // remapping to V

            if constexpr (enable_logs) clog << "Found vc has size " << vc.size() << endl;

            // {
            //     int N = V.size();
            //     VB was(N);
            //     for ( int v : vc ) {
            //         was[v] = true;
            //         for (int d : V[v]) was[d] = true;
            //     }
            //     for (int i=0; i<N; i++) {
            //         if ( !was[i] && !hit_nodes[i] ) clog << "Node " << i << " unhit, V(" << i << "): " << V[i] << endl;
            //     }
            // }

            if(!isCorrect(V, vc, K, hit_nodes)){
                auto domset = vc;
                fillGreedilyToValidSolution(V,domset,K,hit_nodes);
                clog << "Found vc is not a valid solution, filled greedily, now domset.size(): " << domset.size() << endl;

                // assert( isCorrect(V, vc, K, hit_nodes) );
                // do not terminate, just

            // }else return vc;
            }else res = vc;

            // return vc;
        }
    }

    // auto V0 = V;

    int N = V.size();
    VVI sets;
    sets.reserve(N);

    int known_lower_bound = 1;


    int init_iters = 1e3;
    int iterations_done = 0;
    int reductions_frequency = 2;
    double exponent = 0.3;

    if(N >= 50'000) init_iters = 2e2;

    if(N >= 10'000) reductions_frequency = 4;
    if(N >= 50'000) exponent = 0.5;

    if(N >= 50'000) reductions_frequency = 6;
    if(N >= 100'000) exponent = 0.6;


    if(find_exact_result) exponent = 0.25;

    bool solution_found = false;

    if(K==1 && res.empty()) {
        if (S.size() < res.size() && !S.empty()) res = S;
        if constexpr (enable_logs) clog << endl << "Creating fallback solution" << endl;
        fillGreedilyToValidSolution(V,res,K,hit_nodes);
        sw.start("fallback solution creation");
        if(hs_track) {
            res = VI(N); iota(ALL(res),0);
            VVI __sets; __sets.reserve(N);
            for( int i=0; i<N; i++ ) if(!hit_nodes[i]) {
                __sets.push_back(V[i]);
                __sets.back().push_back(i);
                REMCVAL(excluded_nodes,__sets.back());
                if(__sets.back().empty()) __sets.pop_back();
            }
            HSLS::trimHsToNodesInSets(__sets,res);
            assert(HSLS::isCorrectHS(__sets,res));

            int millis_left = sw.getLimit("main") - sw.getTime("main");
            // if(V.size() > 1'000 && V.size() <= 50'000 && millis_left >= 1000) {
            //     DSSE dsse(V, hit_nodes, excluded_nodes);
            //     millis_left *= 0.3;
            //
            //     clog << "Solving using CPSAT for " << ceil(millis_left / 1000) << " seconds" << endl;
            //     dsse.exact_hs_solving_method = CPSAT;
            //     auto r = dsse.findMHSForSets(__sets, CPSAT, millis_left);
            //     if(!r.empty()) res = r;
            //     DEBUG(res.size());
            // }

            tie(res,sets_always_hit) = HSLS::hsImprovementLS(__sets, res, hit_nodes, sw,
                // 250 * __sets.size(), 1,false,false,false);
                50 * __sets.size(), 1,false,false,false);
                // 15 * __sets.size(), 1,false,false,false);

            assert( isCorrect(V,res,K,hit_nodes) );

            res_iters = __sets.size();
            res_sets = __sets;
        }

        // if (recursion_level <= 3){ // just for tests, rather nothing useful...
        //     int millis_left = sw.getLimit("main") - sw.getTime("main");
        //     res = findDSOfHSGraph(V, 0.25 * millis_left);
        //     {
        //         VVI __sets; __sets.reserve(N);
        //         for( int i=0; i<N; i++ ) if(!hit_nodes[i]) {
        //             __sets.push_back(V[i]);
        //             __sets.back().push_back(i);
        //             REMCVAL(excluded_nodes,__sets.back());
        //             if(__sets.back().empty()) __sets.pop_back();
        //         }
        //         HSLS::fillByHSToValidHS(sets, res);
        //     }
        //     exit(2);
        // }

        res = ds21swaps(V, res, 1, 5,false);
        // assert(isCorrect(V,res,K,hit_nodes));
        int ITERS = 7; // #TEST default value = 7
        for ( int i=0; i<ITERS; i++ ) {
            // DEBUG(i);
            res = ds21swaps(V, res, 3, 5,false);
            // assert(isCorrect(V,res,K,hit_nodes));
        }
        sw.stop("fallback solution creation");
        if constexpr (enable_logs) clog << "Initial fast fallback 2-1-swaps result size: " << res.size() << endl << endl;
        if constexpr (enable_logs) clog << "Fallback solution created in "
             << sw.getTime("fallback solution creation") / 1000 << "sec" << endl;
        // exit(1);
        fallback_res = res;
        sort(ALL(fallback_res));

        assert( isCorrect(V,res,K,hit_nodes) );
    }

    // exit(1);

    constexpr bool remove_excluded_nodes_from_constraints = false; // #CAUTION - this does not work correctly yet...
    auto removeExcluded = [&]( VI & r ) { REMCVAL(excluded_nodes,r); };

    // bool very_large_graph_case = (V.size() > 3e5); // #TEST
    // bool very_large_graph_case = (V.size() > 5e4); // original
    // bool very_large_graph_case = (V.size() > 5e4 && res.size() > 10'000);
    bool very_large_graph_case = (V.size() > 5e4 || res.size() > 10'000 || GraphUtils::countEdges(V) > 5e5); // original

    bool use_soft_large_graph_condition = true; // #TEST original value false
    if( use_soft_large_graph_condition ) {
        very_large_graph_case = (V.size() > 1e4 || res.size() > 500 || GraphUtils::countEdges(V) > 1e5); // original

        // int M = GraphUtils::countEdges(V);
        // very_large_graph_case |= (V.size() > 1e4 && M >= 3.5 * V.size()) || res.size() > 500;
    }

    if (is_vc_case) very_large_graph_case = true;
    // if res.size() is small, then graph is 'dense', then iterative approach works visibly better, but a bit slower :(

    if(find_exact_result) very_large_graph_case = false;

    // very_large_graph_case = false; // #TEST


    // if (very_large_graph_case) init_iters = max(init_iters, max( (int)res.size(), N / 20 ) ); // original
    if (very_large_graph_case) init_iters = max(init_iters, max( (int)res.size()/2, N / 10 ) ); // #TEST
    const int init_iters0 = init_iters;

    if constexpr (enable_logs) DEBUG(very_large_graph_case);

    if(initS.empty()) {
        // for(int i=0; i<N; i++) if( V[i].empty() ) S.push_back(i);
        // if( !S.empty()) sets.push_back(S);

        // constexpr bool create_initial_constraints = false;
        bool create_initial_constraints = very_large_graph_case;
        create_initial_constraints |= use_only_full_hsls;

        if (create_initial_constraints) {
            bool use_full_constraints = false;
            use_full_constraints |= use_only_full_hsls;

            int init_constraints = 0.93*N; // original
            if(hs_track) {
                init_constraints = 0.97*N;
                // init_constraints = N;
                // init_iters = max(1'000, N / 30);
                // init_iters = max((int)res.size(), N/5);
                init_iters = (res.size() + N + sets.size()) / 5;
            }
            // int init_constraints = 0.9*N;
            // int init_constraints = N / 2;
            // int init_constraints = 2*N / 3;
            if (use_full_constraints) {
                init_constraints = N;
                init_iters = N/10; // #TEST
            }
            if constexpr (enable_logs) clog << "Creating initial <= " << init_constraints << " constraints" << endl;

            // S = CombinatoricUtils::getRandomSubset(N-1,init_constraints);
            { // equivalently, but thread safe, as it does not use UniformIntGenerator
                S.resize(N);
                iota(ALL(S),0);
                StandardUtils::shuffle(S);
                S.resize(init_constraints);
            }

            VB was(N);
            VI dst(N,inf);
            for( int v : S ) if (!hit_nodes[v]) {
                auto reachables = findReachableNodesFromSWithinDistanceK(V,{v},K,dst,was);
                if constexpr (remove_excluded_nodes_from_constraints) removeExcluded(reachables);
                sets.push_back(reachables);
            }

            if constexpr (enable_logs)
                clog << "There are " << sets.size() << " initial constraints created, S.size(): " << S.size() << endl;

            bool find_good_init_hs = true;
            if(find_good_init_hs) {
                if constexpr (enable_logs) clog << "Finding initial hs" << endl;
                if(K == 1) {
                    if (use_full_constraints && !res.empty()) S = res; // res should be valid as a fallback solution
                    else {
                        if (!res.empty()) S = res;
                        else fillGreedilyToValidSolution(V,S,K,hit_nodes);
                        // fillGreedilyToValidSolution(V,S,K,hit_nodes);
                        S = ds21swaps(V,S,1,3);
                        // for ( int i=0; i<7; i++ ) S = ds21swaps(V,S,3, 5);
                        HSLS::trimHsToNodesInSets(sets,S);

                        // HSLS hsls(sets, S, hit_nodes, sw);
                        // S = hsls.hsImprovementLS(sets, S, hit_nodes, sw, 2 * sets.size(), 1,
                        //     false, false, false);
                    }
                    assert(HSLS::isCorrectHS(sets,S,hit_nodes));
                    // assert(isCorrect(V,S,K,hit_nodes));
                }
                else {
                    HSLS hsls(sets, S, hit_nodes, sw);
                    tie(S,sets_always_hit) = hsls.hsImprovementLS(sets, S, hit_nodes, sw, 5 * sets.size(), 1, false, false);
                }
            }

            // if(very_large_graph_case) { // #TEST - making only small variations
            //     IntGenerator rnd;
            //     shuffle(sets, rnd);
            //     sets.resize( 0.95 * sets.size() );
            //     // sets.resize( 0.8 * sets.size() );
            //     HSLS::trimHsToNodesInSets(sets,S);
            // }
        }

     }else {

         clog << "Running baselineHG with nonempty initS, initS.size(): " << initS.size() << endl;
         assert(isCorrect(V,initS,K,hit_nodes));
         if ( initS.size() < res.size() || res.empty() ) res = initS;
         if ( fallback_res.empty() || initS.size() < fallback_res.size() ) fallback_res = initS;

         {
             double F = 1.0;
             if constexpr (enable_logs) clog << "Initializing with initS and random " << F * 100 << "% of all sets to hit" << endl;

             S = initS;
             VI dst(N,inf);
             VB was(N);

             int probab = 92; // 90 works ok
             IntGenerator rnd;

             // for( int i=0; i<N; i++ ) if( !hit_nodes[i] ) {
             for( int i=0; i<N; i++ ) if( !hit_nodes[i] && rnd.nextInt(101) <= probab ) {
                 auto reachables = findReachableNodesFromSWithinDistanceK(V,{i},K,dst,was);
                 if constexpr (remove_excluded_nodes_from_constraints) removeExcluded(reachables);
                 sets.emplace_back( reachables );
             }

             sets.resize(F * sets.size());
             HittingSetLS::trimHsToNodesInSets(sets,S);
         }


         if(false){
             int max_cnt = 2.0*GraphUtils::countEdges(V) / ( 4*N );
             max_cnt = max(max_cnt,1);

             VI dst(N,inf);
             VB was(N), was2(N), was3(N);
             S.clear();

             for( int v : initS ) {
                 assert(!V[v].empty());
                 if( V[v].empty() ) continue;
                 StandardUtils::shuffle(V[v]);

                 if(!was2[v]) {
                     auto reachables = findReachableNodesFromSWithinDistanceK(V,{v},K, dst,was);
                     if constexpr (remove_excluded_nodes_from_constraints) removeExcluded(reachables);
                     sets.push_back(reachables);
                     was2[v] = true;

                     if(!was3[v]) {
                         S.push_back(v);
                         was3[v] = true;
                     }
                 }
                 int cnt = 0;
                 for( int d : V[v] ) {
                     if(!was2[d]) {
                         auto reachables = findReachableNodesFromSWithinDistanceK(V,{d},K, dst,was);
                         if constexpr (remove_excluded_nodes_from_constraints) removeExcluded(reachables);
                         sets.push_back(reachables);
                         was2[d] = true;

                         if(!was3[d]) {
                             was3[d] = true;
                             S.push_back(d);
                         }
                         cnt++;
                         if(cnt == max_cnt) break;
                     }
                 }
             }
             assert(HittingSetLS::isCorrectHS(sets,S, hit_nodes));
         }
     }

    if constexpr (use_only_full_hsls) {
        if constexpr (enable_logs) clog << "use_only_full_hsls set to true, using only HSLS improvements" << endl;

        bool remove_excluded = true;
        if(remove_excluded) {
            for( auto & v : sets ) REMCVAL( excluded_nodes, v );
            for(int i=(int)sets.size()-1; i>=0; i--) if( sets[i].empty() ) REM(sets,i);
        }

        if (!res.empty()) {
            S = res;
            HSLS::trimHsToNodesInSets(sets,S);
            HSLS::fillByHSToValidHS(sets,S);
        }
        else {
            S = VI(N);
            iota(ALL(res),0);
            HSLS::trimHsToNodesInSets(sets,S);
        }

        IntGenerator rnd;

        bool use_tabu = false;
        while (!sw.tle()) {
            const int iters = 5 * (sets.size() + S.size());
            tie(S,sets_always_hit) = HSLS::hsImprovementLS(sets,S,hit_nodes, sw, iters, 1,
                false, use_tabu, false, true);
            use_tabu = !use_tabu;
            assert(isCorrect(V,S,K,hit_nodes));

            if(!remove_excluded) S = ds21swaps(V,S,1,10,false);

            // for( int i=0; i<S.size()/50; i++ ) REM(S,rnd.nextInt(S.size()));
            // HSLS::fillByHSToValidHS(sets,S);
        }

        if ( S.size() < res.size() ) res = S;

        return res;
    };


    // int solution_found = false;

    VB helper(N);
    int iterations_since_last_improvement = 0;
    int iterations_since_last_best_improvement = 0;
    int large_iterations_done = 0;
    int small_perturbations_done_since_last_large = 0;

    IntGenerator rnd;


    bool use_aux_hit_nodes = false;
    VI aux_hit_nodes;
    if(use_aux_hit_nodes) {
        constexpr double PERC = 1; // at most one decimal place admitted here
        for( int i=0; i<N; i++ ) if(!hit_nodes[i] && rnd.nextInt(1001) <= 10*PERC ) {
            hit_nodes[i] = true;
            aux_hit_nodes.push_back(i);
        }
    }

    auto start_time = sw.getTime("main");
    auto limit_time = sw.getLimit("main");
    auto max_time_spent = limit_time - start_time;
    auto getTimeLeft = [&]() { return limit_time - sw.getTime("main"); };
    auto hasTimePassedForAuxHitNodes = [&](){ return getTimeLeft() < 0.75 * max_time_spent; };


    constexpr bool add_constraints_from_smallest = false;
    if constexpr (add_constraints_from_smallest){
        clog << "Clearing sets and finding a VC of only deg-2 constraints-induced graph W" << endl;
        sets.clear();
        VVI W(N);
        for ( int i=0; i<N; i++ ) if ( !hit_nodes[i] && V[i].size() == 2 ) {
            int a = V[i][0], b = V[i][1];
            W[a].push_back(b);
            W[b].push_back(a);
            sets.emplace_back();
            sets.back().push_back(a);
            sets.back().push_back(b);
            if (!excluded_nodes[i])
                sets.back().push_back(i);
        }
        double time_left_sec = (sw.getLimit("main") - sw.getTime("main")) / 1000.0;

        NuMVC numvc;
        int seed = rnd.nextInt(1e9);
        VI mis = numvc.solve( W, 0.1 * time_left_sec, {}, 1, seed );
        VI vc = CombinatoricUtils::getFullSetDifference(W.size(), mis);
        S = vc;

        clog << "Found a VC of only degree-2 constraints of size " << vc.size() << endl;
        // exit(2);

        // exponent = 0.1;
        init_iters = 3*N;
        hs_track = true; // #TEST
    }

    int cur_constraints_size = 2;
    auto getNodesForConstraintOfNextFixedSize = [&]() {
        VI res;
        int max_deg = 0;
        for (auto & v : V) max_deg = max(max_deg, (int)v.size());
        while ( cur_constraints_size < max_deg && res.empty() ) {
            cur_constraints_size++;
            for ( int i=0; i<N; i++ ) if (!hit_nodes[i] && V[i].size() == cur_constraints_size) res.push_back(i);
        }
        return res;
    };
    auto getAllConstraintOfNextFixedSize = [&]() {
        cur_constraints_size++;
        VVI res;
        for ( int i=0; i<N; i++ )if (!hit_nodes[i] && V[i].size() == cur_constraints_size){
            VI temp = V[i];
            if ( !excluded_nodes[i] ) temp.push_back(i);
            res.push_back(temp);
        }

        return res;
    };

    vector<ULL> hashes(N);
    for (int i=0; i<N; i++) hashes[i] = rnd.rand();
    auto removeAlwaysHitSetsFromSets = [&](VVI & sets, VVI & always_hit_sets) {
        if (always_hit_sets.empty()) return;
        set<ULL> to_remove;
        for (auto & v : always_hit_sets) {
            ULL h = 0;
            for (int d : v) h ^= hashes[d];
            to_remove.insert(h);
        }

        for ( int i=(int)sets.size()-1; i>=0; i-- ) {
            assert(!sets[i].empty());
            ULL h = 0;
            for (int d : sets[i]) h ^= hashes[d];
            if ( to_remove.contains(h) ) REM(sets,i);
        }
    };


    while(!sw.tle() || (large_iterations_done == 0)) {
        large_iterations_done++;

        const int max_unreachables = pow(N,exponent)+1;
        // const int max_unreachables = pow(N,0.43)+1;
        // auto furrthest_unreachables = findFurthestUnreachableNodes(V,S,K, max_unreachables);
        VI furrthest_unreachables;


        if constexpr (add_constraints_from_smallest) furrthest_unreachables = getNodesForConstraintOfNextFixedSize();
        else furrthest_unreachables = findUnreachableNodesWithLargestDegree(V,S,K, hit_nodes, max_unreachables);

        while( !furrthest_unreachables.empty() && !sw.tle() ) {
            // ENDL(1);

            // clog << "furrthest_unreachables.size(): " << furrthest_unreachables.size() << endl;
            sw.start("findReachableNodesFromSWithinDistanceK");
            VI dst(N,inf);
            VB was(N);

            // constexpr bool use_greedy_filling = true;
            // bool use_greedy_filling = (iterations_done & 1);
            bool use_greedy_filling = ((iterations_done>>2) & 1);
            // bool use_greedy_filling = (large_iterations_done & 1);
            if( rnd.nextInt(5) == 0 ) use_greedy_filling = !use_greedy_filling;
            // bool use_greedy_filling = (rnd.nextInt(2) == 0);
            // constexpr bool fill_with_hs_of_reachables = false;
            bool fill_with_hs_of_reachables = (true && !add_constraints_from_smallest);

            int nodes_added = 0;
            if (use_greedy_filling) fill(ALL(helper),false);

            int lb_red = furrthest_unreachables.size();


            constexpr bool induce_from_fallback = true;


            if (fill_with_hs_of_reachables) {
                VVI to_hit;
                VI zb;
                if(use_greedy_filling) sort(ALL(furrthest_unreachables),
                [&](int a, int b){ return V[a].size() < V[b].size(); });
                // StandardUtils::shuffle(furrthest_unreachables);
                // if(use_greedy_filling) sort(ALL(furrthest_unreachables),
                // [&](int a, int b){ return V[a].size() > V[b].size(); });

                for(auto v : furrthest_unreachables) {
                    if( use_greedy_filling ) if( helper[v] ) continue;
                    auto reachables = findReachableNodesFromSWithinDistanceK(V,{v},K, dst, was);
                    if constexpr (remove_excluded_nodes_from_constraints) removeExcluded(reachables);
                    to_hit.push_back(reachables);
                    sets.push_back(reachables);
                    // zb.push_back(v); // original
                    zb.push_back( reachables[0] ); // should also work if excluded nodes are considered
                    if constexpr (!remove_excluded_nodes_from_constraints) {
                        assert(reachables[0] == v);
                        assert(!reachables.empty()); // this can potentially happen if all nodes in N[v] are
                        // marked as excluded
                    }

                    if (use_greedy_filling) {
                        if( nodes_added++ == max_unreachables ) break;
                        for( int d : reachables ) helper[d] = true;
                    }
                }
                if (use_greedy_filling) fill(ALL(helper),false);

                // if constexpr (remove_excluded_nodes_from_constraints)
                    StandardUtils::makeUnique(zb);

                if constexpr (!induce_from_fallback) {
                    // auto tempS = HSLS::hsImprovementLS(to_hit, zb, hit_nodes, sw, init_iters, 1, true);
                    VI tempS;
                    tie(tempS,sets_always_hit) = HSLS::hsImprovementLS(to_hit, zb, hit_nodes, sw, 2*to_hit.size(), 1, true);
                    // auto tempS = HSLS::hsImprovementLS(to_hit, zb, hit_nodes, sw, 2*to_hit.size(), 1, false); // #TEST
                    for(int d : S) helper[d] = true;
                    for(int d : tempS) if(!helper[d]) S.push_back(d);
                    for(int d : S) helper[d] = false;
                    if constexpr (enable_logs) clog << "zb.size(): " << zb.size() << ", tempS.size(): " << tempS.size() << endl;
                    lb_red = tempS.size();

                    assert(HittingSetLS::isCorrectHS(to_hit,tempS));
                }
                else{
                    VI tempS;
                    if (fallback_res.empty()) {
                        // auto tempS = HSLS::hsImprovementLS(to_hit, zb, hit_nodes, sw, init_iters, 1, true);
                        tie(tempS,sets_always_hit) = HSLS::hsImprovementLS(to_hit, zb, hit_nodes, sw, init_iters, 1, true);
                    }else {
                        tempS = fallback_res; // #TEST - it might be better to use fallback_res instead of res... ?
                        HSLS::trimHsToNodesInSets(to_hit,tempS);
                        // tempS = HSLS::hsImprovementLS(to_hit, tempS, hit_nodes, sw, to_hit.size(), 1, true);
                        tie(tempS,sets_always_hit) = HSLS::hsImprovementLS(to_hit, tempS, hit_nodes, sw, 5*(to_hit.size()+tempS.size()), 1, false);

                        // if(!res.empty()) fallback_res = res; // #TEST
                    }

                    for(int d : S) helper[d] = true;
                    for(int d : tempS) if(!helper[d]) S.push_back(d);
                    for(int d : S) helper[d] = false;
                    if constexpr (enable_logs) clog << "zb.size(): " << zb.size() << ", tempS.size(): " << tempS.size() << endl;
                    lb_red = tempS.size();

                    assert(HittingSetLS::isCorrectHS(to_hit,tempS));
                }
            }else {
                assert(false && "should fill in with hs of unhit sets...");
                assert(add_constraints_from_smallest);
                clog << "Adding " << furrthest_unreachables.size() << " constraints of size "
                     << cur_constraints_size << endl;
                VVI new_sets; new_sets.reserve(furrthest_unreachables.size());
                for (int d : furrthest_unreachables) {
                    new_sets.emplace_back(V[d]);
                    new_sets.back().push_back(d);
                    S.push_back(V[d][0]);
                }
                StandardUtils::makeUnique(S);
                sets += new_sets;
            }
            sw.stop("findReachableNodesFromSWithinDistanceK");


            int iters = init_iters;
            if( iterations_done == 0 ) iters /= 2;
            // if constexpr ( !induce_from_fallback )
            {
                // reductions_frequency = 4; // #TEST

                sw.start("hsImprovementLS2-1");
                // int lb = min(1,(int)S.size()-(int)furrthest_unreachables.size()); // original
                // int lb = min(1,(int)S.size()-lb_red - 3); // original
                int lb = min((int)(0.4 * S.size()),(int)S.size()-lb_red - 3); // original
                bool reduce = ( (iterations_done % reductions_frequency) > 0 );
                // if(!solution_found) reduce = true; // #TEST

                reduce = true;
                if(hs_track) reduce = false;

                // reduce = false;
                if(find_exact_result) {
                    iters = 10*sets.size();
                    lb = 1;
                    reduce = true;
                }

                constexpr int variant = 1;
                if constexpr (variant == 1) {
                    tie(S,sets_always_hit) = HSLS::hsImprovementLS(sets, S, hit_nodes, sw, iters, lb , reduce);
                } else{
                    reduce = false; // #TEST
                    tie(S,sets_always_hit) = HSLS::hsImprovementLS(sets, S, hit_nodes, sw, sets.size(), lb , reduce, iterations_done&1);
                }
                sw.stop("hsImprovementLS2-1");
            }

            constexpr int FREQ = inf;
            // constexpr int FREQ = 20;
            if( (iterations_done % FREQ == FREQ-1) && (K == 1) ) {
                fillGreedilyToValidSolution(V, S, K, hit_nodes);
                S = ds21swaps(V, S, 1, 1, false);
                HSLS::trimHsToNodesInSets(sets,S);
            }

            sw.start("findFurthestUnreachableNodes");

            // if constexpr (add_constraints_from_smallest)
            // furrthest_unreachables = getNodesForConstraintOfNextFixedSize();

            if (use_greedy_filling) {
                furrthest_unreachables = findUnreachableNodesWithLargestDegree(V,S,K, hit_nodes, max_unreachables);
            }
            else furrthest_unreachables = findUnreachableNodesWithLargestDegree(V,S,K, hit_nodes, max_unreachables);
            sw.stop("findFurthestUnreachableNodes");

            int total_elements_in_sets = accumulate(ALL(sets),0, [&](int s, auto & v){ return s + v.size(); });
            if constexpr (enable_logs) clog << "After iteration #" << iterations_done << " there are " << sets.size()
                 << " sets to hit and S.size(): " << S.size() << ", total_elements_in_sets: " << total_elements_in_sets
                 << ", time: " << sw.getTime() / 1000 << endl;

            iterations_done++;

        }

        if( !isCorrect(V,S,K, hit_nodes) ) {
            assert(sw.tle());
            // S += findFurthestUnreachableNodes(V,S,K, hit_nodes, inf);
            DSS::fillGreedilyToValidSolution(V, S, K, hit_nodes);
        }

        if(K == 1 && (rnd.nextInt(3) == 0)) {
        // if(K == 1 && (rnd.nextInt(2) == 0)) {
        // if(K == 1) { // #TEST
        // if(false) { // #TEST
            // assert(isCorrect(V,S,K, hit_nodes));
            // S = ds21swaps(V, S, 1, 1,false);
            S = ds21swaps(V, S, 1, 5,false);
            // assert(isCorrect(V,S,K, hit_nodes));
            // assert( HSLS::isCorrectHS(sets,S,hit_nodes) );
        }

        auto updateAns = [&](){
            if(res.empty()){ res = S; res_sets = sets; res_iters = init_iters; }
            if( S.size() < res.size() ) {
                res = S; res_sets = sets; res_iters = init_iters;
                iterations_since_last_best_improvement = 0;
            }else iterations_since_last_best_improvement++;

            if( S.size() == res.size() ) res = S;
        };
        updateAns();

        if(sw.tle()) break;

        int avg_deg = 2*GraphUtils::countEdges(V)/N;
        if constexpr (enable_logs) DEBUG(avg_deg);
        if constexpr (enable_logs) DEBUG(iterations_since_last_best_improvement);
        // if(avg_deg <= 70) {
        if (false) // #TEST - disable using swaps here
        if(V.size() <= 1e4) {
            if( large_iterations_done > 10 )
            if( K == 1 && !sw.tle() && ((rnd.nextInt(8 ) == 0) || iterations_since_last_improvement > 1 )){
                // HSLS::trimHsToNodesInSets(sets,S);

                // 2-1/1-1-swaps are a good method of perturbations and creating random states of the same size
                // #CAUTION! For very dense graphs, this is much more time-consuming than hitting-set approach, as
                // there are few sets to hit. For those cases it should be disabled or run much less frequently

                // auto S2 = ds21swaps(V, S, 5, 1, false, 2);
                bool enable_21_swaps = ( S.size() <= 50 );
                auto S2 = ds21swaps(V, S, 1, 7, false, 2); // original
                if(enable_21_swaps) S2 = ds21swaps(V, S2, 1, 3, true, 2);
                // S2 = ds21swaps(V, S2, 7, 2, false, 2);
                // auto S2 = ds21swaps(V, S, 2, 3, false, 2);
                // auto S2 = ds21swaps(V, S2, 2, 3, false, 2);
                // S2 = ds21swaps(V, S2, 2, 5, false, 2);
                swap(S,S2);
                // updateAns(); // updating for S2, as it must be a valid solution
                if(isCorrect(V,S,K, hit_nodes)) {
                    if(S.size() < res.size()) {
                        res = S; res_sets = sets; res_iters = init_iters;
                        iterations_since_last_best_improvement = 0;
                    }
                }
                swap(S,S2);

                HittingSetLS::trimHsToNodesInSets(sets,S2);
                if( S2.size() < S.size() ) {
                    if constexpr (enable_logs) clog << "\tImproved S by " << S.size() - S2.size() << " using 2-1/1-1-swaps" << endl;
                }
                S = S2;
                assert(HittingSetLS::isCorrectHS(sets,S, hit_nodes, N));
                // if(isCorrect(V,S,K, hit_nodes)) updateAns();
                if(isCorrect(V,S,K, hit_nodes)){
                    // S need not be a valid solution after trimming hs to nodes in sets
                    if(S.size() < res.size()) {
                        res = S; res_sets = sets; res_iters = init_iters;
                        iterations_since_last_best_improvement = 0;
                    }
                }
            }
        }

        solution_found = true;

        if constexpr (enable_logs) {
            ENDL(1);
            clog << "Found a valid solution of size " << S.size() << endl;
            clog << "After next large iteration (#" << large_iterations_done
                 << "), \n\tbest ssolution size so far: " << res.size() << ", time: " << sw.getTime() / 1000 << endl;
        }

        // if(large_iterations_done % 10 == 0 && !sw.tle()) // original
        if (false) // #TEST - no need to remove dominating sets here, there should be none...
        if(large_iterations_done == 10 && !sw.tle()) // original
        { // removing dominating sets
            int S0 = sets.size();
            HittingSetLS::removeDominatingSets(sets);
            if constexpr (enable_logs)
            if(sets.size() < S0) {
                ENDL(2);
                clog << "Initially sets.size(): " << S0 << endl;
                clog << "After removing dominating sets, sets.size(): " << sets.size() << endl;
                clog << "Dominating sets removed: " << S0 - sets.size() << endl;
                ENDL(2);
            }
            HittingSetLS::trimHsToNodesInSets(sets,S);
        }

        if(!sw.tle()) {
            HSLS::trimHsToNodesInSets(sets,S);
            HSLS::removeUnhitSets(sets,S);

            sw.start("hsls3");
            int iters = 15*init_iters;
            // iters *= 2;
            // iters = max(iters, (int)max(sets.size(),S.size())); // original
            iters = max(iters, (int)min(sets.size(),2*S.size())); // #TEST

            // int lb = 0.9 * S.size();
            int lb = 0.8 * S.size(); // #TEST
            // int lb = 0.97 * res.size(); // #TEST
            // int lb = max(0.95 * res.size(), 0.9*S.size()); // #TEST
            // int lb = min(0.9 * res.size(), 0.9*S.size()); // #TEST

            int prev_S_size = S.size();

            bool use_tabu_for_nonhs = ( large_iterations_done & 1 );
            if(rnd.nextInt(5) == 0) use_tabu_for_nonhs = !use_tabu_for_nonhs;

            double avg_deg = 2.0 * GraphUtils::countEdges(V) / N;
            if( avg_deg > 0.05 * N ) use_tabu_for_nonhs = false; // for dense graphs do not use tabu for nonhs nodes

            // if( S.size() <= 30 && N >= 1e3 ) use_tabu_for_nonhs = false; // #TEST for dense graphs do not use tabu
            if( S.size() <= N / 100 ) use_tabu_for_nonhs = false; // #TEST for dense graphs do not use tabu

            use_tabu_for_nonhs &= (large_iterations_done > 10);
            bool admit_sa = true;

            if (very_large_graph_case) {
                lb = 1;
                // use_tabu_for_nonhs = true;
                if( large_iterations_done <= 7 ) use_tabu_for_nonhs = false;
                if( large_iterations_done <= 7 ) admit_sa = false;
            }

            // if( rnd.nextInt(2) > 0 ) use_tabu_for_nonhs = false; // #TEST
            if( rnd.nextInt(3) > 0 ) use_tabu_for_nonhs = false; // #TEST - with probability 2/3 do not use tabu
            // if( rnd.nextInt(2) > 0 ) use_tabu_for_nonhs = true; // #TEST
            // use_tabu_for_nonhs = false;
            if(hs_track) use_tabu_for_nonhs = (large_iterations_done & 1);

            VVI new_sets = sets;

            // bool remove_excluded_nodes = (false || remove_excluded_nodes_from_constraints);
            // bool remove_excluded_nodes = ( (large_iterations_done & 1) || remove_excluded_nodes_from_constraints);
            // bool remove_excluded_nodes = ( ((large_iterations_done % 3) == 0) || remove_excluded_nodes_from_constraints);
            // bool remove_excluded_nodes = false;
            // bool remove_excluded_nodes = ( ((large_iterations_done % 5) == 0) || remove_excluded_nodes_from_constraints);
            bool remove_excluded_nodes = (rnd.nextInt(2) == 0); // just some additional minor diversification
            // bool remove_excluded_nodes = (rnd.nextInt(3) > 0); // just some additional minor diversification

            if(hs_track) remove_excluded_nodes = true;

            // remove_excluded_nodes = true; // #TEST

            if ( remove_excluded_nodes ){
                if constexpr (enable_logs) clog << "Removing excluded nodes from sets" << endl;

                VB prev_excluded_nodes = excluded_nodes;
                if constexpr (!exclude_additional_nodes_at_start)
                if(rnd.nextInt(2) == 0) {
                    int cnt_before = 0;
                    for(int i=0; i<V.size(); i++) cnt_before += excluded_nodes[i];
                    DSReducer::markAdditionalExcludedNodes(V,hit_nodes, excluded_nodes);
                    int cnt_after = 0;
                    for(int i=0; i<V.size(); i++) cnt_after += excluded_nodes[i];
                    if constexpr (enable_logs) clog << "There were " << cnt_after - cnt_before
                         << " nodes additionally marked as excluded in baselineHG" << endl;
                }

                if constexpr (enable_logs) DEBUG(S.size());
                for (auto & v : new_sets) removeExcluded(v);
                for (int i=(int)new_sets.size()-1; i>=0; i--) if ( new_sets[i].empty() ) REM(new_sets,i);
                HSLS::trimHsToNodesInSets(new_sets,S);
                if constexpr (enable_logs) DEBUG(S.size());
                VB r(N);
                for ( int d : S ) r[d] = true;

                VVI remaining_sets_to_hit;
                VI S2;

                for ( auto & v : new_sets ) {
                    bool is_hit = false;
                    for (int d : v) is_hit |= r[d];
                    if (!is_hit) {
                        remaining_sets_to_hit.push_back(v);
                        S2.push_back( v[0] );
                    }
                }

                StandardUtils::makeUnique(S2);
                if (S2.size() >= 2 && !sw.tle()) {
                    // S2 =  HSLS::hsImprovementLS(remaining_sets_to_hit,S2, hit_nodes, sw, iters, 1, false, // #TEST
                    //     use_tabu_for_nonhs, admit_sa );
                    tie(S2,sets_always_hit) =  HSLS::hsImprovementLS(remaining_sets_to_hit,S2, hit_nodes, sw,
                        min( iters/3, 30*(int)remaining_sets_to_hit.size() ),
                        1, false, use_tabu_for_nonhs, false );
                }
                S += S2;
                if constexpr (enable_logs) DEBUG(S2.size());
                if constexpr (enable_logs) DEBUG(S.size());

                for(auto &s : new_sets) assert(!s.empty());

                if(!sw.tle()) {
                    tie(S,sets_always_hit) = HSLS::hsImprovementLS(new_sets,S, hit_nodes, sw, iters,
                        min(lb,max(1,(int)S.size()-1)), false, use_tabu_for_nonhs, admit_sa );
                }

                assert( HSLS::isCorrectHS(new_sets,S,hit_nodes) );
                if(!HSLS::isCorrectHS(sets,S,hit_nodes)) {
                    if constexpr (enable_logs)
                        clog << "After finding HS of new_sets - with removed excluded nodes - "
                                    "it is not a valid HS for sets, filling it back" << endl;
                    HSLS::fillByHSToValidHS(sets,S);
                }

                if(!exclude_additional_nodes_at_start) excluded_nodes = prev_excluded_nodes;
            }else {
                if constexpr (enable_logs) clog << "Not removing excluded nodes from sets" << endl;
                tie(S,sets_always_hit) = HSLS::hsImprovementLS(sets, S, hit_nodes, sw, iters, lb, false,
                    use_tabu_for_nonhs, admit_sa );
            }

            if( isCorrect(V,S,K,hit_nodes) && S.size() < res.size() ) {
                res = S; res_sets = sets; res_iters = init_iters;
                iterations_since_last_best_improvement = 0;
            }

            if(S.size() >= prev_S_size) iterations_since_last_improvement++;
            else iterations_since_last_improvement = 0;

            if constexpr (enable_logs) DEBUG(iterations_since_last_improvement);

            // const int MAX_PERTURB_THR = ( very_large_graph_case ? 2 : 3 );
            constexpr int MAX_PERTURB_THR = 3;
            // if(!sw.tle() && iterations_since_last_improvement > 2 ){
            if(!sw.tle() && iterations_since_last_improvement > MAX_PERTURB_THR ){
            // if( (iterations_since_last_improvement > 2) || ((iterations_since_last_best_improvement % 100) == 0) ){
                iterations_since_last_improvement = 0;

                if constexpr (enable_logs) clog << "Making perturbations" << endl;

                // static int version = 1;
                // version = 1 - version;

                // int version = rnd.nextInt(1);
                int version = 1;

                constexpr int MAX_ITERS_SINCE_BEST = 30;
                // bool use_large_perturbation = (iterations_since_last_best_improvement > MAX_ITERS_SINCE_BEST);
                bool use_large_perturbation = (iterations_since_last_best_improvement > MAX_ITERS_SINCE_BEST)
                                                && ((iterations_since_last_best_improvement % 2) == 0);

                // {
                //     if( (small_perturbations_done_since_last_large % 10) == 0 ) use_large_perturbation = true;
                //     if(use_large_perturbation) small_perturbations_done_since_last_large = 0;
                //     else small_perturbations_done_since_last_large++;
                // }


                // if(use_large_perturbation && find_exact_result) {
                if(find_exact_result) {
                    constexpr bool remove_excluded_nodes_from_sets = false; // #TEST - check if this will not produce WA
                    auto sets2 = sets;
                    swap(sets, sets2);
                    if constexpr (remove_excluded_nodes_from_sets) {
                        for( auto & v : sets ) REMCVAL( excluded_nodes, v );
                        for(int i=(int)sets.size()-1; i>=0; i--) if( sets[i].empty() ) REM(sets,i);
                    }

                   if constexpr (enable_logs)
                       clog << endl << "Solving HS instance for current constraints, sets.size(): " << sets.size() << endl;
                    sw.start("exact_hs_solving");
                    // auto mhs = DSSE::findMHSForSets(sets, exact_hs_solving_method);
                    auto mhs = DSSE::findMHSForSets(sets, exact_hs_solving_method, 1e9, {}, known_lower_bound);
                    // auto mhs = DSSE::findMHSForSets(sets, exact_hs_solving_method,S,known_lower_bound);
                    known_lower_bound = mhs.size(); // #TEST #CAUTION! THIS MIGHT BE INCORRECT IF WE USE PERTURBATIONS!
                    sw.stop("exact_hs_solving");
                    if constexpr (enable_logs) clog << "found mhs of size " << mhs.size() << endl;

                    assert( HittingSetLS::isCorrectHS(sets, mhs, hit_nodes) );
                    if( isCorrect(V,mhs,K,hit_nodes) ) return mhs;
                    int T = 20;
                    while(T--) {
                        if constexpr (enable_logs) clog << "mhs is not a valid DS, trying to modify it, tries left: " << T << endl;
                        tie(mhs,sets_always_hit) = HSLS::hsImprovementLS(sets,mhs,hit_nodes,sw, 2*sets.size(),
                            1,false, true, false);
                        if( isCorrect(V,mhs,K,hit_nodes) ) return mhs;
                    }
                    if constexpr (enable_logs) clog << "did not manage to make mhs a valid DS, continuing with constraint generation..." << endl;

                    swap(sets, sets2);
                    S = mhs;
                    assert( HittingSetLS::isCorrectHS(sets,S,hit_nodes) );
                }
                else
                {
                    // if(version == 0) { // original - removing randomly some number of sets
                    if(use_large_perturbation) { // #TEST- using both perturbation methods...

                        assert( HittingSetLS::isCorrectHS(sets,S,hit_nodes) );

                        double F = 0.1;
                        // double F = 0.02;
                        // if(N <= 1000) F = 0.3;
                        // if( (iterations_since_last_best_improvement % 30) == 0) F = 0.1;
                        if constexpr (enable_logs) {
                            ENDL(1);
                            clog << "Using large perturbation" << "\n";
                            clog << "No improvement found, trimming random " << 100*F << "% of sets" << endl;
                            ENDL(1);
                        }
                        StandardUtils::shuffle(sets);
                        int new_sets_size = (int)((1.0-F) * sets.size());
                        if ( new_sets_size > 0 && new_sets_size < sets.size() ) sets.resize(new_sets_size);
                        HittingSetLS::trimHsToNodesInSets(sets,S);
                        tie(S,sets_always_hit) = HSLS::hsImprovementLS(sets, S,hit_nodes, sw,  iters, 1, false ); // original
                    }

                    // if(use_large_perturbation) {
                    //     S = res;
                    //     sets = res_sets;
                    // }

                    // if(version == 1) { // remove 1% of sets
                    //     double F = 0.01;
                    //     if(use_large_perturbation) F = 0.1;
                    //     ENDL(1);
                    //     if(use_large_perturbation) clog << "Using large perturbation" << "\n";
                    //     clog << "No improvement found, trimming random " << 100*F << "% of sets" << endl;
                    //     ENDL(1);
                    //     StandardUtils::shuffle(sets);
                    //     int new_sets_size = (int)((1.0-F) * sets.size());
                    //     if ( new_sets_size > 0 && new_sets_size < sets.size() ) sets.resize(new_sets_size);
                    //     HittingSetLS::trimHsToNodesInSets(sets,S);
                    //     // S = HSLS::hsImprovementLS(sets, S,hit_nodes, sw,  iters, 1, false ); // original
                    // }

                    // const bool revert_to_best_res_state = use_large_perturbation;
                    bool revert_to_best_res_state = (use_large_perturbation || ( iterations_since_last_best_improvement > 3 * MAX_PERTURB_THR ));
                    if(very_large_graph_case) revert_to_best_res_state = true;
                    // const bool revert_to_best_res_state = false; // set to false to use 'standard' perturbations

                    if(hs_track) revert_to_best_res_state = true;

                    // revert_to_best_res_state = false;

                    if(revert_to_best_res_state && res_iters != -1) {
                        if constexpr (enable_logs) {
                            clog << "No improvement found, reverting to best res state (almost)" << endl;
                            DEBUG(res.size());
                            DEBUG(res_iters);
                        }

                        // if( iterations_since_last_best_improvement > 3 * MAX_PERTURB_THR )
                            // res_iters *= 1.01;
                        if(K == 1) res = ds21swaps(V,res,1,5);

                        S = res;

                        sets = res_sets; // original
                        // {// #TEST
                        //     // HSLS::trimHsToNodesInSets(sets,S);
                        //     shuffle(sets,rnd);
                        //     if(sets.size() > res_sets.size()) sets.resize(res_sets.size());
                        //     // HSLS::trimHsToNodesInSets(sets,S);
                        // }

                        HSLS::trimHsToNodesInSets(sets,S);
                        init_iters = res_iters;

                        // StandardUtils::shuffle(sets);
                        // shuffle(sets,rnd);
                        // for (int i=0; i<2 ; i++)
                        //     if (sets.size() > 2) sets.pop_back();
                        // HSLS::trimHsToNodesInSets(sets,S);
                        HSLS::removeUnhitSets(sets,S);

                        VVI cur_sets;
                        if (remove_excluded_nodes) {
                            cur_sets = sets;
                            for (auto & v : sets) removeExcluded(v);
                            for (int i=(int)sets.size()-1; i>=0; i--) if ( sets[i].empty() ) REM(sets,i);
                            HSLS::trimHsToNodesInSets(sets,S);
                            HSLS::removeUnhitSets(sets,S);
                        }

                        // bool remove_random_subset = (S.size() > 50);
                        bool remove_random_subset = (S.size() > 25) && (rnd.nextInt(2) == 0);
                        // bool remove_random_subset = false;
                        if(remove_random_subset){

                            bool remove_sets = false;
                            bool remove_nodes = true;
                            bool remove_nodes_from_vicinity = !remove_nodes;
                            // bool remove_sets = rnd.nextInt(2);
                            // bool remove_nodes = rnd.nextInt(2);
                            int to_remove = 0;

                            if(remove_sets) {
                                // double F = 0.01;
                                // F *= 1 + rnd.nextInt(5);
                                // to_remove = F * sets.size() + 1;
                                to_remove = 0.005 * sets.size();
                                // to_remove = 0.01 * sets.size();
                                if(to_remove > 0) {
                                    shuffle(sets,rnd);
                                    sets.resize(sets.size() - to_remove);
                                    HSLS::trimHsToNodesInSets(sets,S);
                                }
                            }

                            if(remove_nodes){
                                double F = 0.01;
                                // F *= 1 + rnd.nextInt(3);
                                // F *= 1 + rnd.nextInt(5);
                                to_remove = F * S.size() + 1;
                                // to_remove = min(to_remove,5);
                                StandardUtils::shuffle(S);
                                S.resize(S.size() - to_remove);

                                // HSLS::fillByHSToValidHS(sets, S);

                                HSLS::removeUnhitSets(sets,S);
                                HSLS::trimHsToNodesInSets(sets,S);

                                // if(rnd.nextInt(2)) HSLS::fillByHSToValidHS(sets, S);
                                // else {
                                //     HSLS::removeUnhitSets(sets,S);
                                //     HSLS::trimHsToNodesInSets(sets,S);
                                // }
                            }

                            if(remove_nodes_from_vicinity){
                                // double F = 0.01;
                                // double F = 0.01 * (3 + rnd.nextInt(5)); // with distance 2
                                double F = 0.01 * (3 + rnd.nextInt(3)); // with distance 3
                                shuffle(S,rnd);
                                to_remove = F * S.size() + 1;
                                VI removed; removed.reserve(to_remove);

                                const bool remove_single_node_and_do_not_fill = false;
                                if ( remove_single_node_and_do_not_fill ) to_remove = 3; // #TEST

                                for(int i=0; i<to_remove; i++) removed.push_back(S[i]);

                                VI dst(N,inf);
                                VB was(N);
                                constexpr int MAX_DST = 4;
                                auto vicinity = findReachableNodesFromSWithinDistanceK(V,removed,MAX_DST, dst,was);
                                // REMCVAL(excluded_nodes,vicinity);

                                for( int d : vicinity) was[d] = true;
                                int c = 0;
                                for(int d : S) c += was[d];
                                const int MAX_S = S.size() / 5; // original
                                if( c > MAX_S ) {
                                    for(int d : vicinity) was[d] = false;
                                    shuffle(vicinity,rnd);
                                    // int new_size = MAX_S; // orginal
                                    int new_size = 1.0 * MAX_S / c * vicinity.size();
                                    if(new_size > 0) vicinity.resize( new_size);

                                    for(int d : vicinity) was[d] = true;
                                    c = 0;
                                    for(int d : S) c += was[d];
                                }
                                REMCVAL(was,S);
                                for( int d : vicinity) was[d] = false;

                                if ( !remove_single_node_and_do_not_fill ) HSLS::fillByHSToValidHS(sets, S);
                                else {
                                    HSLS::removeUnhitSets(sets,S);
                                    HSLS::trimHsToNodesInSets(sets,S);
                                }

                                to_remove = c;
                                if constexpr (enable_logs)
                                    clog << "Removing " << removed.size() << " nodes and all nodes in hs from dst="
                                     << MAX_DST << "from those, cnt " << c << endl;
                            }

                            if( isCorrect(V,S,K,hit_nodes) && S.size() <= res.size() ) res = S;
                            if constexpr (enable_logs)
                                clog << "After removing " << to_remove << " random nodes/sets from S and filling using HS, "
                                    "S.size(): " << S.size() << endl;
                        }

                        assert(HSLS::isCorrectHS(sets,S));
                        tie(S,sets_always_hit) = HSLS::hsImprovementLS(sets, S, hit_nodes, sw,
                            5*(sets.size() + S.size()), max((int)S.size()-3, 1),
                            false, true, false, true );
                        if(isCorrect(V,S,K,hit_nodes) && S.size() <= res.size()) res = S;

                        if (remove_excluded_nodes) {
                            sets = cur_sets;
                            HSLS::fillByHSToValidHS(sets,S);
                        }

                        // if (!sw.tle()) {
                        //     double F = 0.05;
                        //     int newsize = 1 + F * sets_always_hit.size();
                        //     if (newsize > 0) {
                        //         shuffle(sets_always_hit,rnd);
                        //         sets_always_hit.resize(newsize);
                        //     }
                        //
                        //     clog << "Removing from " << sets.size() << " sets " << sets_always_hit.size() << " always hit sets" << endl;
                        //     removeAlwaysHitSetsFromSets(sets,sets_always_hit);
                        //     clog << "After removing, sets.size(): " << sets.size() << endl;
                        //     HSLS::trimHsToNodesInSets(sets,S);
                        // }

                        // iterations_since_last_best_improvement = max(iterations_since_last_best_improvement-MAX_PERTURB_THR,0);
                    }else {
                        if(version == 1) { // removing randomly some number of nodes from current hitting set
                            // double F = 0.05;
                            double F = 0.03;
                            if(use_large_perturbation) F *= 3;
                            StandardUtils::shuffle(S);
                            if constexpr (enable_logs)
                                clog << "No improvement found, removing random " << 100*F << "% nodes from S" << endl;
                            int new_S_size = (int)((1.0-F) * S.size());
                            if(use_large_perturbation && new_S_size > 0 && new_S_size < S.size()) {
                                new_S_size = min( new_S_size, max( 1, (int)S.size()-5 ) );
                            }
                            if (new_S_size > 0) S.resize( new_S_size );
                            HittingSetLS::removeUnhitSets(sets,S);
                            HittingSetLS::trimHsToNodesInSets(sets,S);

                            tie(S,sets_always_hit) = HSLS::hsImprovementLS(sets, S,hit_nodes, sw,  iters, 1, false ); // original
                            // HittingSetLS::fillGreedilyToValidSolution(V,S,K,hit_nodes);
                            // HittingSetLS::trimHsToNodesInSets(sets,S);
                        }
                    }

                    // if(iterations_since_last_best_improvement > MAX_ITERS_SINCE_BEST + 5)
                    // // if(iterations_since_last_best_improvement > MAX_ITERS_SINCE_BEST + rnd.nextInt(10))
                    //     iterations_since_last_best_improvement = 0;

                    if(!revert_to_best_res_state) {
                        if(use_large_perturbation) init_iters /= 1.3;
                        else init_iters /= 1.09;
                    }
                    // else init_iters /= 1.03;


                    // just a precaution, so that we do not land in a situation where init_iteers falls to zero...
                    init_iters = max(init_iters, min(1000, (int)sets.size()));

                    // init_iters /= 1.09; // original
                }
            }else {
                if constexpr (enable_logs) {
                    DEBUG(res.size());
                    DEBUG(S.size());
                }
            }

            sw.stop("hsls3");

            if constexpr (enable_logs) clog << "Leaving hsls3" << endl;
        }

        assert(HittingSetLS::isCorrectHS(sets,S, hit_nodes));

        init_iters *= 1.03;

        init_iters = min( (int)1e7, init_iters );


        if( use_aux_hit_nodes && !aux_hit_nodes.empty() && hasTimePassedForAuxHitNodes() ) {
            if constexpr (enable_logs) clog << "Adding back auxiliary hit nodes!!" << endl;
            for( int v : aux_hit_nodes ) hit_nodes[v] = false;
            aux_hit_nodes.clear();

            if(false){ // alternative - fill greedily nodes that are not hit and add them to solutions
                VB was(N);
                for(int d : res) was[d] = true;
                for( int i=0; i<N; i++ ) {
                    bool hit = (was[i] || hit_nodes[i]);
                    for( int d : V[i] ) hit |= was[d];
                    if(!hit) {
                        was[i] = true;
                        res.push_back(i);
                    }
                }

                assert( isCorrect(V,res,K, hit_nodes) );
                S = res;

                { // removing 20% of sets, randomly, then restart init_iters... - this somehow clears the whole state
                    StandardUtils::shuffle(sets);
                    int new_sets_size = (int)ceil( 0.66 * sets.size());
                    // int new_sets_size = (int)ceil( 0.9 * sets.size());
                    sets.resize(new_sets_size);
                    HSLS::trimHsToNodesInSets(sets, S);
                }

                init_iters = init_iters0; // resetting...
                iterations_since_last_best_improvement = 0;
                iterations_since_last_improvement = 0;
                assert( isCorrect(V,res,K, hit_nodes) );
            }

            if(true){
                if(!res.empty()) S = res;
                // else S += findFurthestUnreachableNodes(V,S,K, hit_nodes, inf);
                else DSS::fillGreedilyToValidSolution(V, S, K, hit_nodes);

                VVI new_sets_to_hit;
                VI new_hs;
                VB hit(N);
                VI dst(N,inf);
                VB was(N);
                {
                    auto reachables = findReachableNodesFromSWithinDistanceK(V, S, K, dst,was);
                    if constexpr (remove_excluded_nodes_from_constraints) removeExcluded(reachables);
                    for( int d : reachables ) hit[d] = true;
                }
                for(int i=0; i<N; i++) if(!hit[i] && !hit_nodes[i]) {
                    auto reachables = findReachableNodesFromSWithinDistanceK(V, {i}, K, dst,was);
                    if constexpr (remove_excluded_nodes_from_constraints) removeExcluded(reachables);
                    new_sets_to_hit.push_back( reachables );
                    new_hs.push_back(i);
                }

                int iters = 10 * new_sets_to_hit.size();
                tie(new_hs,sets_always_hit)  = HSLS::hsImprovementLS(new_sets_to_hit, new_hs, hit_nodes, sw, iters, 1, false, false );
                tie(new_hs,sets_always_hit) = HSLS::hsImprovementLS(new_sets_to_hit, new_hs, hit_nodes, sw, iters, 1, false, true );
                if constexpr (enable_logs) {
                    DEBUG(new_sets_to_hit.size());
                    DEBUG(new_hs.size());
                    DEBUG(S.size());
                }
                S += new_hs;
                if constexpr (enable_logs) {
                    DEBUG(S.size());
                }
                assert( isCorrect(V,S,K, hit_nodes) );
                if(!isCorrect(V,res,K, hit_nodes)) res = S;

                { // removing 20% of sets, randomly, then restart init_iters... - this somehow clears the whole state
                    StandardUtils::shuffle(sets);
                    // int new_sets_size = (int)ceil( 0.75 * sets.size());
                    // int new_sets_size = (int)ceil( 0.85 * sets.size());
                    int new_sets_size = (int)( 0.85 * sets.size());
                    sets.resize(new_sets_size);
                    HSLS::trimHsToNodesInSets(sets, S);
                }

                init_iters = init_iters0; // resetting...
                iterations_since_last_best_improvement = 0;
                iterations_since_last_improvement = 0;
            }
        }

        bool use_aux_pert = false;
        if(use_aux_pert && iterations_since_last_improvement > 1){
            int ind = rnd.nextInt(S.size());
            REM(S,ind);
            HSLS::removeUnhitSets(sets,S);
            HSLS::trimHsToNodesInSets(sets,S);
        }

    } // end of while

    if ( !isCorrect(V,S,K,hit_nodes) ) {
        DSS::fillGreedilyToValidSolution(V, S, K, hit_nodes);
        if(K == 1) res = ds21swaps(V, res, 1, 2,false); // #TEST
        if constexpr (enable_logs) clog << "After filling, S.size(): " << S.size() << ", while best result res.size(): " << res.size() << endl;
    }
    if ( S.size() < res.size() ) res = S;

    if( use_aux_hit_nodes && !aux_hit_nodes.empty() ) {
        for( int v : aux_hit_nodes ) hit_nodes[v] = false;
        aux_hit_nodes.clear();
        DSS::fillGreedilyToValidSolution(V, res, K, hit_nodes);
        if(K == 1) res = ds21swaps(V, res, 1, 2,false); // #TEST
    }

    // if(!isCorrect(V,res,K,hit_nodes)) DSS::fillGreedilyToValidSolution(V, res, K, hit_nodes);
    assert(isCorrect(V,res,K, hit_nodes));
    // assert(isCorrect(V0,res,K, hit_nodes));

    return res;
}

