//
// Created by sylwe on 07/05/2025.
//

#include "DSReducer.h"

#include "DominatingSetSolver.h"

#include <GraphInducer.h>
#include <GraphUtils.h>
#include <StandardUtils.h>
#include <Stopwatch.h>
#include <components/BridgesAndArtPoints.h>
#include <components/ConnectedComponents.h>

#include "CollectionOperators.h"
#include "DSSE.h"
#include "Pace25Utils.h"


void DSReducer::markAdditionalExcludedNodes(VVI &V, VB &hit, VB &excluded) {
    int N = V.size();

    for ( int v = 0; v<N; v++ ) if( !V[v].empty() && !excluded[v] && !hit[v] ) {
        int cnt = 0, only_unhit_neighbor = -1;
        for (int d : V[v]) {
            cnt += hit[d];
            only_unhit_neighbor = ( hit[d] ? only_unhit_neighbor : d );
        }
        bool cond = (cnt == V[v].size());
        cond |= (cnt >= V[v].size()-1 && (only_unhit_neighbor == -1 || !excluded[only_unhit_neighbor]));

        if (cond) excluded[v] = true;
    }
}

tuple<VI,VB,VB,VI,vector<LiftableRule*>> DSReducer::reductionRulesDS(VVI & V, int time_limit_millis,
                                                                  const bool only_basic_reductions) {
    if(V.empty()) return { {}, {}, {}, {}, {} };
    for (auto & v : V) sort(ALL(v));

    int N = V.size();
    VB was(N);
    VB hit(N);
    if (!hit_nodes.empty()) {
        assert( hit_nodes.size() == N );
        hit = hit_nodes;
    }

    VB excluded(N);
    if ( !excluded_nodes.empty() ) {
        assert(excluded_nodes.size() == N);
        excluded = excluded_nodes;
    }

    if (permanent_excluded_node_unhit_dominator.empty()) {
        // clog << "WARNING! permanent_excluded_node_unhit_dominator not set in DSReducer::reductionRulesDS" << endl;
        permanent_excluded_node_unhit_dominator.resize(N);
        iota(ALL(permanent_excluded_node_unhit_dominator),0);
    }else assert(permanent_excluded_node_unhit_dominator.size() == N);

    for (int d : permanent_excluded_node_unhit_dominator) assert( d >= 0 && d < N );

    // VI to_remove;
    vector<LiftableRule*> to_lift;

    constexpr bool write_logs_and_stats = false && enable_logs;
    constexpr bool make_measurements = true;
    if constexpr( write_logs_and_stats ) clog << "Starting reduction rules for DS" << endl;

    constexpr bool use_rules_for_excluded = true; // this seems to be buggy, even if basic_rules_for_exlucded are not used...
    constexpr bool use_lossy_rules_for_excluded = true; // it seems that lossy rules are not lossy at all... :)


    VI kernel;
    int excluded_and_hit_cnt = 0;
    int hit_edges_removed = 0;
    int excluded_edges_removed = 0;
    int path_rules_applied = 0;
    int path_rules2_applied = 0;
    int path_rules3_applied = 0;
    int path_rules3_applied_value_2 = 0;
    int path_rules3_applied_value_3 = 0;
    int path_rules3_applied_value_4 = 0;
    int path_rules3_applied_value_5 = 0;
    int domination_rules_applied = 0;
    int domination_rules2_applied = 0;
    int domination_rules3_applied = 0;
    int domination_rules4_applied = 0;
    int domination_n123_rules_applied = 0;
    int domination_n123_2nodes_rules_applied = 0;
    int bipartite_domination_rules_applied = 0;
    int art_point_rules_applied = 0;
    int funnel_folding_rules_applied = 0;
    // int funnel_domination_rules_applied = 0;
    int funnel3_nonfolding_rules_applied = 0;
    int funnel4_nonfolding_applied = 0;
    int funnel5_nonfolding_applied = 0;
    int funnel6_nonfolding_applied = 0;
    int funnel7_nonfolding_applied = 0;
    int small_conn_comp_considered = 0;
    int excluded_domination_applied = 0;
    int basic_excluded_marked = 0;
    int hit_n2_cnt = 0;
    int clique_N2_rules_applied = 0;
    int funnel2_nonfolding_applied = 0;
    int recursive_reducer_applied = 0;

    // VB dom2_nodes_considered(N);

    if ( hit_nodes.empty() || recursive_reductions_level == 0 )
    for(int i=0; i<N; i++) assert(!V[i].empty());

    VB helper(N);
    VB in_kernel(N);
    Stopwatch timer;
    const string prepr_opt = "prepr";
    if constexpr (make_measurements) timer.start("all_used_rules");

    timer.setLimit(prepr_opt,time_limit_millis);
    timer.start(prepr_opt);
    constexpr int TIMER_CHECK = (1 << 10);

    // for( auto & v : V ) sort(ALL(v));


    deque<int> basic_que;
    VI basic_degs(N,0);

    bool changes = true;

    VVI neighbors_marked_to_remove(N);
    for( int i=0; i<N; i++ ) neighbors_marked_to_remove[i].reserve(5);

    auto checkAndUnmarkExcludedNode = [&](int v) {
        if( V[v].empty() || V[permanent_excluded_node_unhit_dominator[v]].empty()) {
            excluded[v] = false;
            // is_unhit_dominator[permanent_excluded_node_unhit_dominator[v]] = false;
            permanent_excluded_node_unhit_dominator[v] = v;
        }
    };

    auto removeHitAndExcludedNodes = [&]() {
        for ( int v = 0; v<N; v++ ) checkAndUnmarkExcludedNode(v);

        bool removed = false;

        for ( int v=0; v<N; v++ ) if ( hit[v] && excluded[v] && !V[v].empty() ) {
            int cnt_unhit_deg1_neighbor = 0, w = -1;
            for ( int d : V[v] ) {
                cnt_unhit_deg1_neighbor += ( !hit[d] && V[d].size() == 1 );
                if( !hit[d] && V[d].size() == 1 ) w = d;
            }
            if ( cnt_unhit_deg1_neighbor > 0 ) {
                // DEBUG(cnt_unhit_deg1_neighbor);
                kernel.push_back(v);
                in_kernel[v] = true;
                to_lift.push_back( new ReducibleRule(v) );
                hit[v] = true;
                for ( int d : V[v] ) hit[d] = true;
                excluded_and_hit_cnt++;
            }

            GraphUtils::removeNodeFromGraph(V, v);
            removed = true;
            changes = true;
        }
        return removed;
    };

    const VB full_mask(N,true);

    auto basicEdgeRemoval = [&](VB nodes_to_check = {}) {
        if (nodes_to_check.empty()) nodes_to_check = full_mask;

        if constexpr (use_lossy_rules_for_excluded)
            for ( int v=0; v<N; v++ ) checkAndUnmarkExcludedNode(v);

        bool edge_removed = false;

        for ( int v=0; v<N; v++ ) if ( (hit[v] || (use_rules_for_excluded && excluded[v])) && nodes_to_check[v] ) {

            if constexpr(use_lossy_rules_for_excluded) {
                auto & zb = V[v];
                for (int i=(int)zb.size()-1; i>=0; i--) {
                    bool a = hit[v] && hit[zb[i]];
                    bool b = excluded[v] && excluded[zb[i]];
                    hit_edges_removed += a && (v < zb[i]);
                    if constexpr (use_lossy_rules_for_excluded) excluded_edges_removed += b && (v < zb[i]);
                    int s1 = zb.size();
                    if ( a || b ) {
                        REM(zb,i);
                    }
                    edge_removed |= zb.size() != s1;
                }
            }else {
                auto fun = [&](int ind){ return (hit[v] && hit[V[v][ind]]);  };
                int s1 = V[v].size();
                REMCFUN(fun, V[v]);
                edge_removed |= V[v].size() != s1;
            }
        }

        return edge_removed;
    };

    auto basic_rules = [&]() {

        if constexpr (make_measurements) timer.start("basic rules");
        {
            assert(count(ALL(was),true) == 0);
            assert(count(ALL(helper),true) == 0);
            fill(ALL(in_kernel),false);
            for(int d : kernel) in_kernel[d] = true;
        }

        if(true) if(basic_que.empty()) {
            // If basic_que is not empty, then only these nodes in the que can be affected by basic_rules, as these
            // are the only new leaves that were created. Also no new nodes were marked as excluded hit
            // (those that were were already removed from the graph), so no need to rerun edge removal

            if constexpr (make_measurements) timer.start("basic-edge-removal");
            basicEdgeRemoval();
            if constexpr (make_measurements) timer.stop("basic-edge-removal");
        }

        constexpr bool use_fast_basic_rules = true; // for most cases this is only slightly faster

        // if constexpr (!use_fast_basic_rules) {
        //     if(true){ // if v is a leaf and is hit, then if its neighbor is also a leaf, it is added to solution
        //         for( int v=0; v<N; v++ ) {
        //             if( V[v].size() == 1 && hit[v] ) {
        //                 // changes = true;
        //                 {
        //                     int w = V[v][0];
        //                     if( V[w].size() == 1 && !hit[w] ) {
        //                         hit[w] = true;
        //                         for( int d : V[w] ) hit[d] = true;
        //                         kernel.push_back(w);
        //                         assert(!in_kernel[w]); in_kernel[w] = true;
        //                         to_lift.push_back( new ReducibleRule(w) );
        //                         GraphUtils::removeNodeFromGraph(V,w);
        //                     }
        //                 }
        //                 GraphUtils::removeNodeFromGraph(V,v);
        //             }
        //         }
        //     }
        //
        //     // if(changes) continue;
        //
        //     if(true){ // if v is a leaf and is not hit, then add N(v) to solution
        //
        //         basic_que.clear();
        //         for(int i=0; i<N; i++) if (V[i].size() == 1 && !hit[i]) basic_que.push_back(i);
        //
        //         // for( int v=0; v<N; v++ ) {
        //         while(!basic_que.empty()) {
        //             int v = basic_que.front();
        //             basic_que.pop_front();
        //
        //             if( V[v].empty() ) continue;
        //             if(hit[v]) continue;
        //             if( V[v].size() != 1 ) continue;
        //
        //             int v_neigh = V[v][0];
        //             kernel.push_back(v_neigh);
        //             assert(!in_kernel[v_neigh]); in_kernel[v_neigh] = true;
        //             to_lift.push_back( new ReducibleRule(v_neigh) );
        //             hit[v_neigh] = true;
        //             for(int d : V[v_neigh]) hit[d] = true;
        //             for(int d : V[v_neigh]) if(d != v) basic_que.push_front(d);
        //
        //             changes = true;
        //             GraphUtils::removeNodeFromGraph(V, v_neigh);
        //         }
        //     }
        //
        //     if(true){ // this should never happen if edges between hit nodes are removed
        //         // if N[v] is hit, then v can be removed from the graph
        //         // if an excluded node is hit, then it can be removed ?? - probably not
        //         for( int v=0; v<N; v++ ) if (!V[v].empty() && hit[v]) {
        //             bool N_hit = hit[v];
        //             // bool excluded_and_hit = ( excluded[v] && hit[v] );
        //
        //             for( int d : V[v] ) N_hit &= hit[d];
        //
        //             if( N_hit ) {
        //                 changes = true;
        //                 GraphUtils::removeNodeFromGraph(V,v);
        //             }
        //             // else if ( excluded_and_hit ) { // #TEST - commenting this made some failed stress tests to pass
        //             //     excluded_and_hit_cnt += (excluded_and_hit && !N_hit); // here equivalent to excluded_and_hit_cnt++
        //             //     changes = true;
        //             //     GraphUtils::removeNodeFromGraph(V,v);
        //             // }
        //         }
        //     }
        // }

        if constexpr (use_fast_basic_rules) {
            bool continue_trimming_and_edge_removal = true;
            while (continue_trimming_and_edge_removal){
                continue_trimming_and_edge_removal = false;

                const bool add_to_que = basic_que.empty();
                if( add_to_que ) for( int i=0; i<N; i++ ) if( V[i].size() == 1 ) basic_que.push_back(i);

                // que.clear(); // #TEST = 'merging' this with N2_hit rule...
                // VI basic_degs(N,0);
                for(int i=0; i<N; i++) {
                    basic_degs[i] = V[i].size();
                    // if(V[i].size() == 1) que.push_back(i); // #TEST = 'merging' this with N2_hit rule...
                    neighbors_marked_to_remove[i].clear();
                }

                VB is_removed(N);
                VB nodes_to_check_for_edge_removal(N,false);

                while(!basic_que.empty()) {
                    int v = basic_que.front();
                    basic_que.pop_front();

                    if( basic_degs[v] != 1 ) continue;

                    int w = -1; // the only neighbor of v
                    for( int d : V[v] ) w = ( is_removed[d] ? w : d );

                    changes = true;

                    if( hit[v] ) {
                        if( basic_degs[w] == 1 && !hit[w] ) { // add w to the solution
                            // assert( !hit[w] ); // this cannot happen if edges between hit nodes were removed
                            kernel.push_back(w);
                            to_lift.push_back( new ReducibleRule(w) );
                            hit[w] = true;
                            // now removing w from graph
                            V[w].clear();
                            is_removed[w] = true;
                        }else {
                            if( basic_degs[w] == 1 ) {
                                is_removed[w] = true;
                                V[w].clear();
                            }else {
                                neighbors_marked_to_remove[w].push_back(v);
                            }
                        }
                        basic_degs[w]--;
                        if(basic_degs[w] == 1) basic_que.push_front(w);

                    }else { // add w to the solution and remove it from the graph
                        kernel.push_back(w);
                        to_lift.push_back( new ReducibleRule(w) );
                        hit[w] = hit[v] = true;
                        for( int d : V[w] ) {
                            neighbors_marked_to_remove[d].push_back(w);
                            hit[d] = true;
                            nodes_to_check_for_edge_removal[d] = true;
                            basic_degs[d]--;
                            if( basic_degs[d] == 1 ) basic_que.push_front(d);
                        }
                        basic_degs[w] = 0;
                        is_removed[w] = true;
                        V[w].clear();

                        basic_degs[v] = 0;
                        V[v].clear();
                    }

                    // removing v from the graph
                    basic_degs[v] = 0;
                    is_removed[v] = true;
                    V[v].clear();
                }

                // now updating neighborhoods
                for( int i=0; i<N; i++ ) {
                    if (!neighbors_marked_to_remove[i].empty()) {
                        for( int d : neighbors_marked_to_remove[i] ) was[d] = true;
                        REMCVAL( was, V[i] );
                        for( int d : neighbors_marked_to_remove[i] ) was[d] = false;
                        neighbors_marked_to_remove[i].clear();
                    }
                }

                bool check_for_edge_removal = false;
                VB nodes_to_check_for_edge_removal2(N,false);
                for (int i=0; i<N; i++) if (nodes_to_check_for_edge_removal[i]) {
                    nodes_to_check_for_edge_removal2[i] = true;
                    check_for_edge_removal = true;
                    for (int d : V[i]) nodes_to_check_for_edge_removal2[d] = true;
                }

                assert(basic_que.empty());

                if (check_for_edge_removal) {
                    if constexpr (make_measurements) timer.start("basic-edge-removal");
                    continue_trimming_and_edge_removal |= basicEdgeRemoval(nodes_to_check_for_edge_removal2);
                    if constexpr (make_measurements) timer.stop("basic-edge-removal");
                }
            }

            assert(basic_que.empty());
        }

        if constexpr (make_measurements) timer.stop("basic rules");


    };

    auto bipartite_domination = [&]() {
        if constexpr (make_measurements) timer.start("bipartite_domination");

        constexpr int inf = 1e9;
        VI dst(N,inf);
        VI X,Y;
        deque<int> que;

        auto bfs = [&](int beg) {
            X.clear();
            Y.clear();
            que.clear();
            que.push_back(beg);
            dst[beg] = 0;
            bool res = true;

            while(!que.empty()) {
                int v = que.front();
                que.pop_front();

                if ( dst[v] & 1 ) Y.push_back(v);
                else X.push_back(v);

                for(int d : V[v]) {
                    if(dst[d] == dst[v]) res = false;
                    if(dst[d] == inf) {
                        dst[d] = dst[v]+1;
                        que.push_back(d);
                    }
                }
            }
            return res;
        };

        VI to_remove;
        for( int i=0; i<N; i++ ) if(!V[i].empty() && dst[i] == inf) {
            if( bfs(i) ) {
                int x_unhit = 0;
                int y_unhit = 0;
                for (int d : X) x_unhit += !hit[d];
                for (int d : Y) y_unhit += !hit[d];

                // { // just an assertion
                //     for (int d : X) was[d] = true;
                //     for ( int d : X ) for(int dd : V[d]) assert(!was[dd]);
                //     for (int d : X) was[d] = false;
                //
                //     for (int d : Y) was[d] = true;
                //     for ( int d : Y ) for(int dd : V[d]) assert(!was[dd]);
                //     for (int d : Y) was[d] = false;
                // }

                if (x_unhit >= 2 && y_unhit >= 2) {
                    VI rem;
                    for ( int d : X ) {
                        int c = 0;
                        for (int dd : V[d]) c += !hit[dd];
                        // if ( c == y_unhit ){ to_remove.push_back(d); bipartite_domination_rules_applied++; break;}
                        if ( c == y_unhit ){ rem.push_back(d); break;}
                    }
                    for ( int d : Y ) {
                        int c = 0;
                        for (int dd : V[d]) c += !hit[dd];
                        // if ( c == x_unhit ){ to_remove.push_back(d); bipartite_domination_rules_applied++; break;}
                        if ( c == x_unhit ){ rem.push_back(d); break;}
                    }
                    if(rem.size() == 2) {
                        to_remove += rem;
                        bipartite_domination_rules_applied++;
                    }
                }
                else if ( X.size() == 1 && y_unhit >= 1 ) to_remove = {X[0]};
                else if ( Y.size() == 1 && x_unhit >= 1 ) to_remove = {Y[0]};
            }
        }

        if (!to_remove.empty()) {
            // clog << "Found valid nodes to remove using bipartite_domination, to_remove.size(): "
                 // << to_remove.size() << endl;

            changes = true;
            for ( int d : to_remove ) {
                hit[d] = true;
                for (int dd : V[d]) hit[dd] = true;
                kernel.push_back(d);
                in_kernel[d] = true;
                to_lift.push_back( new ReducibleRule(d) );
                GraphUtils::removeNodeFromGraph(V,d);
            }
        }

        if constexpr (make_measurements) timer.stop("bipartite_domination");
    };

    auto basic_rules_for_excluded = [&](bool only_first_one = false) {
        if constexpr (!use_rules_for_excluded) return false;
        if constexpr (make_measurements) timer.start("basic rules for excluded");

        bool removed_node = false;

        if (true) {

            if constexpr (use_lossy_rules_for_excluded) removed_node |= removeHitAndExcludedNodes();
            else {
                for ( int v = 0; v<N; v++ ) checkAndUnmarkExcludedNode(v);
            }

            for ( int v = 0; v<N; v++ ) if( !V[v].empty() && !excluded[v] && !hit[v] ) {
                constexpr bool use_stronger_version = false;

                if constexpr (!use_stronger_version) {
                    { // original version - v0
                        bool has_only_hit_neighbors = true;
                        for (int d : V[v]) has_only_hit_neighbors &= hit[d];
                        if (has_only_hit_neighbors) {
                            changes = excluded[v] = true;
                            basic_excluded_marked++;
                        }
                    }
                }

                if constexpr (use_stronger_version) { // stronger version - v1
                    int cnt = 0, only_unhit_neighbor = -1;
                    for (int d : V[v]) {
                        cnt += hit[d];
                        only_unhit_neighbor = ( hit[d] ? only_unhit_neighbor : d );
                    }

                    if(only_unhit_neighbor != -1) checkAndUnmarkExcludedNode(only_unhit_neighbor);

                    // if (cnt >= V[v].size()-1 && (only_unhit_neighbor == -1 || !excluded[only_unhit_neighbor])) {
                    if ( ( (V[v].size() >= 4 && cnt == V[v].size()-1) || cnt == V[v].size() ) // LOSSSY RULE! For V[v].size() >= 2 it is not safe...
                        && (only_unhit_neighbor == -1 || !excluded[only_unhit_neighbor])) {

                        // if( cnt < V[v].size() ) {
                        //     ENDL(2); DEBUG(v); DEBUGV(V,v); DEBUGV(hit,v); DEBUGV(excluded,v);
                        //     for( int d : V[v] ) { DEBUGV(V,d) DEBUGV(hit,d); DEBUGV(excluded,d); }
                        //     ENDL(2);
                        // }

                        changes = excluded[v] = true;

                        permanent_excluded_node_unhit_dominator[v] = v;
                        // permanent_excluded_node_unhit_dominator[v] = only_unhit_neighbor;

                        // is_unhit_dominator[permanent_excluded_node_unhit_dominator[v]] = true;
                        basic_excluded_marked++;
                    }
                }
            }
        }


        if (!only_first_one) {
            // two previous version joined
            for ( int v=0; v<N; v++ ) if(!V[v].empty() && !hit[v]  ) {
                int cnt = 0, w = -1;
                for ( int d : V[v] ) {
                    cnt += !excluded[d];
                    w = (excluded[d] ? w : d);
                }

                if (!excluded[v] && cnt == 0) { // second rule
                    changes = true;
                    hit[v] = true;
                    for (int d : V[v]) hit[d] = true;
                    GraphUtils::removeNodeFromGraph(V,v);
                    kernel.push_back(v);
                    in_kernel[v] = true;
                    to_lift.push_back( new ReducibleRule(v) );
                    removed_node = true;
                    // continue;
                }

                if ( excluded[v] && cnt == 1 ) { // third rule
                    changes = true;
                    hit[w] = true;
                    for (int d : V[w]) hit[d] = true;
                    GraphUtils::removeNodeFromGraph(V,w);
                    kernel.push_back(w);
                    in_kernel[w] = true;
                    to_lift.push_back( new ReducibleRule(w) );
                    removed_node = true;
                    // continue;
                }
            }
        }

        if constexpr (make_measurements) timer.stop("basic rules for excluded");

        return removed_node;
    };


    auto hit_N2 = [&]() {

        if constexpr (make_measurements) timer.start("Hit N2");
        VI N2; N2.reserve(10);
        constexpr int MAX_DEG = 200; // we do not want to check nodes with large degree, as it is time-consuming...

        // for(int i=0; i<N; i++) assert( basic_degs[i] == V[i].size() );

        for (int v = 0; v < N; v++) {
            if (V[v].empty() || V[v].size() > MAX_DEG || hit[v]) continue;
            if (v % TIMER_CHECK == 0) if (timer.tle(prepr_opt)) break;

            bool N2_hit = true;
            for (int d : V[v]) N2_hit &= (V[d].size() <= MAX_DEG);

            if (N2_hit) {
                for (int d : V[v]) was[d] = true;
                for (int d : V[v]) {
                    // for( int d2 : V[d] ) if( d2 != v && !was[d2] ) N2_hit &= hit[d2];
                    for (int d2 : V[d]) {
                        if (d2 != v && !was[d2]) N2_hit &= hit[d2];
                        if (!N2_hit) break;
                    }
                    if (!N2_hit) break;
                }
                for (int d : V[v]) was[d] = false;
            }

            if (N2_hit) {
                // changes = true; // #TEST - merging N2 with basic rules
                hit[v] = true;
                for (int d : V[v]) hit[d] = true;
                kernel.push_back(v);
                // assert(!in_kernel[v]); in_kernel[v] = true;
                to_lift.push_back(new ReducibleRule(v));

                constexpr bool use_faster_alternative_merged_with_basic_rules = true;

                if constexpr (!use_faster_alternative_merged_with_basic_rules) {
                    changes = true;
                    auto to_remove = V[v];
                    for (int d : to_remove) GraphUtils::removeNodeFromGraph(V, d);
                    GraphUtils::removeNodeFromGraph(V, v); // this is needless if we removed all neighbors above
                    hit_n2_cnt++;
                }

                if constexpr (use_faster_alternative_merged_with_basic_rules) {
                    // faster alternative for removing all nodes in to_remove (faster if N1 has tight connection to N2)
                    for (int d : V[v]) was[d] = true;
                    was[v] = true;
                    N2.clear();
                    for (int d : V[v]) {
                        basic_degs[d]--;
                        basic_degs[v]--;

                        for (int dd : V[d]) {
                            if ((was[dd] && d < dd && dd != v) || !was[dd]) {
                                basic_degs[d]--;
                                basic_degs[dd]--;
                            }

                            if (!was[dd]) { // dd is in N2
                                if(!helper[dd]) {
                                    helper[dd] = true;
                                    N2.push_back(dd);
                                }
                                if( basic_degs[dd] == 1 ) basic_que.push_back(dd);
                            }
                        }
                    }
                    for( int d : N2 ) REMCVAL(was,V[d]);

                    // assert(basic_degs[v] == 0);
                    // for(int d : V[v]) assert(basic_degs[d] == 0);
                    // for(int d : N2) assert(basic_degs[d] == V[d].size());

                    for(int d : N2) helper[d] = false;
                    for(int d : V[v]) was[d] = false; was[v] = false;
                    for(int d : V[v]) V[d].clear();
                    V[v].clear();
                    hit_n2_cnt++;
                }
            }

            if(!basic_que.empty()) changes = true;

        }
        if constexpr (make_measurements) timer.stop("Hit N2");

        if constexpr (write_logs_and_stats && make_measurements) DEBUG(timer.getTime("Hit N2") / 1000);
    };

    auto domination_rules2 = [&]() {
         if constexpr (make_measurements) timer.start("domination_rules2_applied");

         VI perm(N);
         VI cnt(N,0);
         VI unhit_neighbors_global(N,0);
         for( int v=0; v<N; v++ ) for(int d : V[v]) unhit_neighbors_global[v] += !hit[d];

         VI unhit_neighbors(N,0);
         VI to_remove;

         iota(ALL(perm),0);
         int iter = 0;

         constexpr bool use_faster_version = true;
         if(!use_faster_version) {
             for( int v : perm ) {
                 if( V[v].empty() ) continue;
                 if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;

                 for( int d : V[v] ) unhit_neighbors[d] += !hit[v];

                 to_remove.clear();

                 for(int d : V[v]) {
                     for( int u : V[d] ) {
                         if( u == v ) continue;
                         if( unhit_neighbors_global[u] > V[v].size() ) continue;
                         unhit_neighbors[u] += !hit[d];
                         if( hit[u] && (unhit_neighbors[u] == unhit_neighbors_global[u]) ) to_remove.push_back(u);
                     }
                 }


                 for( int d : V[v] ) { // clearing
                     was[d] = false;
                     cnt[d] = unhit_neighbors[d] = 0;
                     for(int d2 : V[d]) cnt[d2] = unhit_neighbors[d2] = 0;
                 }

                 { // making to_remove unique
                     for( int i=(int)to_remove.size()-1; i>=0; i-- ) {
                         if( was[to_remove[i]] ){ REM(to_remove,i); }
                         else was[to_remove[i]] = true;
                     }
                     for(int d : to_remove) was[d] = false;
                 }

                 for( int u : to_remove ) GraphUtils::removeNodeFromGraph(V,u);
                 domination_rules2_applied += to_remove.size();
                 changes |= !to_remove.empty();
             } // end of domination for rule
         }

         if(use_faster_version){ // faster version
             for( int u : perm ) {
                 if( V[u].empty() || !hit[u] ) continue;
                 if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;

                 int unhit = 0;
                 for( int d : V[u] ) unhit += !hit[d];
                 assert(unhit == V[u].size()); // this should hold if we removed unhit-unhit edges in basic rules
                 assert(unhit >= 2); // this should hold if we removed hit leafes in basic rules

                 int v = -1;

                 for(int d : V[u]) unhit_neighbors[d] = !hit[d];
                 for(int d : V[u]) if(!hit[d]) {
                     for( int d2 : V[d] ) if( (d2 != u) && (++unhit_neighbors[d2] == unhit) ) {
                         v = d2;
                         break;
                     }
                 }

                 for( int d : V[u] ) { // clearing
                     was[d] = false;
                     cnt[d] = unhit_neighbors[d] = 0;
                     for(int d2 : V[d]) cnt[d2] = unhit_neighbors[d2] = 0;
                 }


                 if(v != -1) {
                     GraphUtils::removeNodeFromGraph(V,u);
                     domination_rules2_applied++;
                     changes = true;
                 }
             } // end of domination for rule
         }
         if constexpr (make_measurements) timer.stop("domination_rules2_applied");

        if constexpr (write_logs_and_stats && make_measurements) {
             DEBUG(iter);
             DEBUG(timer.getTime("domination_rules2_applied") / 1000);
        }
     };

     auto domination_n123 = [&]() {
        if constexpr (make_measurements) timer.start("domination_n123_rules_applied");
        VI to_remove;
        VB N1(N), N2(N), N1UH(N);

        VI perm(N);
        iota(ALL(perm),0);
        sort(ALL(perm), [&]( int a, int b ){ return V[a].size() > V[b].size(); });

        int iter = 0;
        // for( int v=0; v<N; v++ ) {
        for( int v : perm ) {
            if(V[v].size() <= 1) continue;
            if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;

            int cnt = 0;
            to_remove.clear();

            for( int d : V[v] ) was[d] = true; was[v] = true;

            for( int d : V[v] ) {
                bool b = false, b2 = false;
                for( int d2 : V[d] ) {
                    b |= !was[d2];
                    b2 |= (!was[d2] && !hit[d2]);
                    if(b && b2) break;
                }
                N1[d] = b;
                N1UH[d] = b2;
            }

            for( int d : V[v] ) {
                if(N1[d] || hit[d]) continue;
                // if(N1[d]) continue;
                bool has_n1uh_neighbor = false;
                bool has_n1uh_unexcluded_neighbor = false;
                // for( int dd : V[d] ) if(was[dd]) has_n1uh_neighbor |= N1UH[dd];
                for( int dd : V[d] ) {
                    has_n1uh_neighbor |= (was[dd] && N1UH[dd]);
                    // if(has_n1uh_neighbor) break;

                    if constexpr (use_lossy_rules_for_excluded) // this probably is not a lossy rule
                    { // this version uses additionally excluded nodes - a node cannot have N1UH unexcluded node
                        checkAndUnmarkExcludedNode(dd);
                        has_n1uh_unexcluded_neighbor |= (was[dd] && N1UH[dd] && !excluded[dd]);
                        if(has_n1uh_unexcluded_neighbor) break;
                    }
                    else {
                        if(has_n1uh_neighbor) break;
                    }
                }
                // if(!has_n1uh_neighbor && !hit[d]) cnt++;
                // else if(!hit[d]) N2[d] = true;

                // cnt += !has_n1uh_neighbor;
                // N2[d] = has_n1uh_neighbor;

                if constexpr (use_lossy_rules_for_excluded) {
                    // cnt += !has_n1uh_neighbor;
                    // N2[d] = has_n1uh_neighbor;

                    cnt += !has_n1uh_unexcluded_neighbor; // #TEST
                    N2[d] = has_n1uh_unexcluded_neighbor; // #TEST
                }
                else {
                    // cnt += !has_n1uh_unexcluded_neighbor;
                    // N2[d] = has_n1uh_unexcluded_neighbor;

                    cnt += !has_n1uh_neighbor;// #TEST
                    N2[d] = has_n1uh_neighbor;// #TEST
                }
                // if(hit[v] && (!cnt)) break;
                if (cnt > 0) break;
            }
            for( int d : V[v] ) was[d] = false;  was[v] = false;

            if(cnt > 0) { // remove N3 and N2, mark N1 as hit
                kernel.push_back(v);
                to_lift.push_back( new ReducibleRule(v) );
                to_remove.push_back(v);
                hit[v] = true;
                for( int d : V[v] ) hit[d] = true;
                for( int d : V[v] ) if(!N1[d]) to_remove.push_back(d); // original
                // for( int d : V[v] ) if(!N1UH[d]) to_remove.push_back(d); // not sure if this is correct...
            }
            // else { // this else statement and reduction is auxiliary - it can be removed if it does not work...
            else if( !hit[v] ) { // this else statement and reduction is auxiliary - it can be removed if it does not work...
                // #CAUTION - there seems to be something wrong with this rule...
                // with condition else if( !hit[v] ) gives good result for test 010, but it must be tested properly
                int n12_cnt = 0, n1uh_cnt = 0;
                // for( int d : V[v] ) if(N1[d] || N2[d]) n12_cnt++;
                // for( int d : V[v] ) if(N1UH[d]) n1uh_cnt++;
                for( int d : V[v] ) n1uh_cnt += N1UH[d];
                if( n1uh_cnt == 1 ) {
                    // for( int d : V[v] ) if(!hit[d]) if(N1[d] || N2[d]) n12_cnt++;
                    for( int d : V[v] ) n12_cnt += ( !hit[d] && (N1[d] || N2[d]) );

                    int w = -1;
                    for(int d : V[v] ) if(N1UH[d]) w = d;
                    // for(int d : V[v] ) if(N1UH[d]){ w = d; break;}
                    int w_n12_cnt = 0;
                    // for( int d : V[w] ) if(!hit[d]) if( d != v && (N1[d] || N2[d]) ) w_n12_cnt++;
                    for( int d : V[w] ) w_n12_cnt += ( d != v && (N1[d] || N2[d]) && !hit[d] );
                    if( w_n12_cnt + ( hit[w] ? 0 : 1 ) == n12_cnt ) {
                        to_remove.push_back(w);
                        to_lift.push_back( new ReducibleRule(w) );
                        kernel.push_back(w);
                        for(int d : V[w]) hit[d] = true;
                    }
                }
            }

            N1[v] = N2[v] = N1UH[v] = false;
            for(int d : V[v]) N1[d] = N2[d] = N1UH[d] = false;

            if(!to_remove.empty()) {
                changes = true;
                domination_n123_rules_applied++;
                for( int d : to_remove ) GraphUtils::removeNodeFromGraph(V, d);
            }
        }
        if constexpr (make_measurements) timer.stop("domination_n123_rules_applied");

        if constexpr (write_logs_and_stats && make_measurements) {
            DEBUG(timer.getTime("domination_n123_rules_applied") / 1000);
        }
    };

    auto domination_rules = [&]() {
        if constexpr (make_measurements) timer.start("domination_rules_applied");

        constexpr bool use_fast_version = true;

        VB was2(N);
        VI perm(N);
        VI cnt(N,0);
        VI unhit_neighbors(N,0);
        iota(ALL(perm),0);
        bool apply_v15 = !timer.tle(prepr_opt); // this should not be set for very large graphs, as it might be quite time-consuming
        int iter = 0;


        if (!use_fast_version) {
            assert(false && "use fast version");
            VI unhit_neighbor(N,-1);
            VI dominated_nodes;
            sort(ALL(perm), [&]( int a, int b ){ return V[a].size() > V[b].size(); });

            for( int v : perm ) {
                if( V[v].empty() ) continue;
                if( hit[v] ) continue;
                if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;

                bool is_dominating = false;
                int dominated_node = -1;
                dominated_nodes.clear();

                for( int d : V[v] ) was[d] = true;

                for( int d : V[v] ) cnt[d]++;
                for( int d : V[v] ) {
                    for( int d2 : V[d] ) {
                        if( d2 == v ) continue;
                        if( V[d2].size() >= V[v].size()+1 ) continue;
                        cnt[d2]++;
                        unhit_neighbors[d2] += !hit[d];
                        if( !hit[d] || unhit_neighbor[d2] == -1 ) unhit_neighbor[d2] = d;

                        bool cond = false;
                        cond |= ( !hit[d2] && cnt[d2] == V[d2].size() && unhit_neighbors[d2] <= 1 );

                        if( cond ) {
                            is_dominating = true;
                            dominated_node = d2;
                            break;
                        }
                        else if( !hit[d2] && (cnt[d2] == V[d2].size()) && was[d2] ) {
                            is_dominating = true;
                            dominated_node = d2;
                            unhit_neighbor[d2] = v;
                            break;
                        }

                        if( !hit[d2] && cnt[d2] == V[d2].size() ) dominated_nodes.push_back(d2);
                    }
                    if(is_dominating) break;
                }

                if( !is_dominating && apply_v15 ) {
                    for(int d : V[v]) was[d] = true;
                    for( int w : dominated_nodes ) {
                        int unhits = 0;
                        for( int d : V[w] ) if( d != v && !hit[d] ){ helper[d] = true; unhits++; }
                        // helper marks unhit nodes from set N(v) \cap N(w)
                        if( unhits > 0 ) {
                            for( int d : V[w] ) if(d != v && V[d].size()-1 >= unhits ) {
                                int c = helper[d];
                                for( int d2 : V[d] ) c += helper[d2];
                                assert( c <= unhits );
                                if( c == unhits ) {
                                    is_dominating = true;
                                    dominated_node = w;
                                    unhit_neighbor[w] = d;
                                    break;
                                } // if
                            } // for
                        } // if
                        for( int d : V[w] ) helper[d] = false;
                        if(is_dominating) break;
                    } // for
                    for(int d : V[v]) was[d] = false;
                }

                if( is_dominating ) {
                    changes = true;
                    assert( dominated_node != -1 );
                    assert( unhit_neighbor[dominated_node] != -1 );
                    to_lift.push_back( new DomRed(dominated_node, unhit_neighbor[dominated_node]) );
                    hit[v] = true;
                    // excluded[dominated_node] = true;
                    // update properly excluded node
                    domination_rules_applied++;
                }

                for( int d : V[v] ) {
                    was[d] = false;
                    cnt[d] = unhit_neighbors[d] = 0;
                    unhit_neighbor[d] = -1;
                    for(int d2 : V[d]) {
                        cnt[d2] = unhit_neighbors[d2] = 0;
                        unhit_neighbor[d2] = -1;
                    }
                }
            } // end of domination for rule
        }

        if (use_fast_version) {
            sort(ALL(perm), [&]( int a, int b ){ return V[a].size() < V[b].size(); });
            VI neighbors(N,0);
            VI v_nodes;
            v_nodes.reserve(1 + sqrt(N));


            for (int u : perm) {
                if ( V[u].empty() || hit[u] ) continue; // u cannot be hit, as it would be removed using dom2
                if(++iter % TIMER_CHECK <= 1 ) if(timer.tle(prepr_opt)) break;

                v_nodes.clear();
                int unhit = 0, unhit_dominator = -1;

                for ( int d : V[u]) unhit += !hit[d];

                for ( int d : V[u] ) {
                    was[d] = true;
                    unhit_neighbors[d] = !hit[d];
                    neighbors[d] = 1;

                    if (unhit_neighbors[d] == unhit) unhit_dominator = d;
                }
                for ( int d : V[u] ) {
                    if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;

                    for ( int d2 : V[d] ) if (d2 != u) {
                        unhit_neighbors[d2] += !hit[d];
                        if (was[d2] && (unhit_neighbors[d2] == unhit)) { // #TEST
                            unhit_dominator = d2; // original
                        }

                        neighbors[d2]++;
                        if ( neighbors[d2] == V[u].size()) {
                            v_nodes.push_back(d2);
                        }
                    }
                }


                if ( !v_nodes.empty() ) {

                    // VI dominators;
                    if (unhit_dominator != -1) {
                        bool add = false;
                        for (int v : v_nodes) if ( !hit[v] ) { //original - works ok
                            changes |= (!hit[v] || (!excluded[u] && use_rules_for_excluded ));
                            domination_rules_applied += (!hit[v] || (!excluded[u] && use_rules_for_excluded ));
                            add |= !hit[v];

                            // if (!hit[v] || (!excluded[u] && use_rules_for_excluded ))
                            //     dominators.push_back(v);

                            hit[v] = true;

                            if constexpr (use_rules_for_excluded) {

                                if ( !excluded[unhit_dominator] ) { // #TEST #CAUTION - weak condition in domination!
                                // if ( !excluded[unhit_dominator] && !excluded[v] ) { // #TEST #CAUTION - weak condition in domination!
                                    excluded[u] = true;
                                    permanent_excluded_node_unhit_dominator[u] = unhit_dominator;
                                    // is_unhit_dominator[unhit_dominator] = true;
                                }
                            }
                        }
                        if (add) {
                            auto red = new DomRed(u, unhit_dominator);
                            // red->dominators = dominators;
                            to_lift.push_back( red ); // original
                        }
                    }
                }

                for (int d : V[u]) was[d] = neighbors[d] = unhit_neighbors[d] = 0;
                for (int d : V[u]) for (int d2 : V[d]) neighbors[d2] = unhit_neighbors[d2] = 0;
            }
        }

        if constexpr (make_measurements) timer.stop("domination_rules_applied");

        if constexpr (write_logs_and_stats && make_measurements) {
            DEBUG(iter);
            DEBUG( timer.getTime("domination_rules_applied") / 1000);
        }
        // exit(5);
    };

     auto domination_rules3 = [&]() {
        if constexpr (make_measurements) timer.start("domination_rules3_applied");

        constexpr bool use_fast_version = true;
        VI perm(N);
        iota(ALL(perm),0);
        VI cnt(N,0);
        int iter = 0;

         if (!use_fast_version) {
             VI dominated_nodes;

             sort(ALL(perm), [&]( int a, int b ){ return V[a].size() > V[b].size(); });

             for( int v : perm ) {
                 if( V[v].empty() || hit[v] ) continue;
                 if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;

                 dominated_nodes.clear();

                 for( int d : V[v] ) cnt[d]++;
                 for(int d : V[v]) for( int u : V[d] ) if(u != v && !hit[u]) {
                     if( ++cnt[u] == V[u].size() ) dominated_nodes.push_back(u);
                 }

                 constexpr int max_dominated_nodes = 64;

                 int u1 = -1, u2 = -1, w = -1;
                 if( dominated_nodes.size() >= 2 && dominated_nodes.size() <= max_dominated_nodes ) {
                     bool found = false;
                     // for( int uu1 : dominated_nodes ) {
                     for( int i=0; i < dominated_nodes.size(); i++ ) {
                         int uu1 = dominated_nodes[i];

                         for( int d : V[uu1] ) helper[d] = true;
                         // for( int uu2 : dominated_nodes ) if( uu1 < uu2 && !helper[uu2] ) {
                         for( int j=i+1; j < dominated_nodes.size(); j++ ) {
                             int uu2 = dominated_nodes[j];

                             if( uu1 < uu2 && !helper[uu2] ) {
                                 for(int d : V[uu2]) if(helper[d]) {
                                     found = true;
                                     u1 = uu1;
                                     u2 = uu2;
                                     w = d;
                                     break;
                                 }
                                 if(found) break;
                             }
                         }
                         for( int d : V[uu1] ) helper[d] = false;
                         if(found) break;
                     }

                     if(found) {
                         assert(!hit[v] && !hit[u1] && !hit[u2]);
                         changes = true;
                         hit[v] = true;
                         to_lift.push_back( new DomRed3( v, u1, u2, w ) );
                         domination_rules3_applied++;
                         // DEBUG(v); DEBUG(u1); DEBUG(u2); DEBUG(w);
                         // DEBUGV(V,v); DEBUGV(V,u1); DEBUGV(V,u2);
                         // for( int d : V[v] ) DEBUGV(V,d);
                         // exit(3);
                     }
                 }

                 for( int d : V[v] ) {
                     cnt[d] = 0;
                     for(int d2 : V[d]) cnt[d2] = 0;
                 }
             } // end of domination for rule
         }

         if (use_fast_version) {
             VVI dominates(N);

             sort(ALL(perm), [&]( int a, int b ){ return V[a].size() < V[b].size(); });
             VB considered(N);
             VI neighbors(N,0);
             VI unhit_neighbors(N,0);

             for (int u : perm) {
                 if ( V[u].empty() || hit[u] ) continue; // u cannot be hit, as it would be removed using dom2
                 if(++iter % TIMER_CHECK <= 1 ) if(timer.tle(prepr_opt)) break;

                 int unhit = 0;

                 for ( int d : V[u]) unhit += !hit[d];
                 if (unhit == 0) continue;

                 for ( int d : V[u] ) {
                     was[d] = true;
                     unhit_neighbors[d] = !hit[d];
                     neighbors[d] = 1;
                 }
                 for ( int d : V[u] ) {
                     if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;
                     for ( int d2 : V[d] ) if (d2 != u) {
                     // for ( int d2 : V[d] ) if (d2 != u && ( V[d2].size() + was[d2] >= V[u].size() )) { // should work
                         unhit_neighbors[d2] += !hit[d];
                         neighbors[d2]++;
                         // if ( neighbors[d2] == V[u].size() && unhit_neighbors[d2] == unhit && !hit[d2] ) {
                         if ( !was[d2] && neighbors[d2] == V[u].size() && unhit_neighbors[d2] == unhit && !hit[d2] ) {
                             dominates[d2].push_back(u);
                         }
                     }
                 }

                 for (int d : V[u]) was[d] = neighbors[d] = unhit_neighbors[d] = 0;
                 for (int d : V[u]) for (int d2 : V[d]) neighbors[d2] = unhit_neighbors[d2] = 0;
             }

             if( !timer.tle(prepr_opt) ) for ( int v=0; v<N; v++ ) if ( !hit[v] && dominates[v].size() >= 2 ) {
                 auto & dom = dominates[v];
                 REMCVAL(hit,dom);
                 sort(ALL(dom), [&](int a, int b){ return V[a].size() < V[b].size(); });
                 int w = -1, u1 = -1, u2 = -1;

                 for (int i=0; i<dom.size(); i++) {
                     int _u1 = dom[i];
                     // if (hit[_u1]) continue;

                     for ( int d : V[_u1] ) was[d] = true;
                     for (int j=i+1; j<dom.size(); j++) {
                         int _u2 = dom[j];
                         // if (hit[_u2]) continue;

                         // if ( !was[_u2] ) for ( int d : V[_u2] ) if ( was[d] ) { u1 = _u1, u2 = _u2, w = d; }
                         if ( !was[_u2] ) for ( int d : V[_u2] ) if ( was[d] && w != v ) { u1 = _u1, u2 = _u2, w = d; }
                         if (w != -1) break;
                     }
                     for ( int d : V[_u1] ) was[d] = false;
                     if (w != -1) break;
                 }

                 if (w != -1) {
                     if (!(!hit[v] && !hit[u1] && !hit[u2])) {
                        DEBUG(v);
                        DEBUG(PII(u1,u2));
                        DEBUG(hit[v]);
                        DEBUG(hit[u1]);
                        DEBUG(hit[u2]);
                        assert(!hit[v] && !hit[u1] && !hit[u2]);
                     }
                     assert(w != v && "if this fails, then add ifs a few lines before to assure that w != v");
                     changes = true;
                     hit[v] = true;
                     to_lift.push_back( new DomRed3( v, u1, u2, w ) );
                     domination_rules3_applied++;
                 }
             }
         }
         if constexpr (make_measurements) timer.stop("domination_rules3_applied");

         if constexpr (write_logs_and_stats && make_measurements) {
             DEBUG(iter);
             DEBUG(timer.getTime("domination_rules3_applied") / 1000);
         }
    };

    auto domination_rules4 = [&]() {
        if constexpr (make_measurements) timer.start("domination_rules4_applied");

         VI perm(N);
         iota(ALL(perm),0);
         // VI cnt(N,0);
         int iter = 0;

         VVI dominates(N);

         sort(ALL(perm), [&]( int a, int b ){ return V[a].size() < V[b].size(); });
         VB considered(N);
         VI neighbors(N,0);
         VI unhit_neighbors(N,0);

         for (int u : perm) { // this is standard copy-pasted from other rules creation of [dominates] vector
             if ( V[u].empty() || hit[u] ) continue; // u cannot be hit, as it would be removed using dom2
             if(++iter % TIMER_CHECK <= 1 ) if(timer.tle(prepr_opt)) break;

             int unhit = 0;

             for ( int d : V[u]) unhit += !hit[d];
             if (unhit == 0) continue;

             for ( int d : V[u] ) {
                 was[d] = true;
                 unhit_neighbors[d] = !hit[d];
                 neighbors[d] = 1;
             }
             for ( int d : V[u] ) {
                 if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;
                 for ( int d2 : V[d] ) if (d2 != u) {
                 // for ( int d2 : V[d] ) if (d2 != u && ( V[d2].size() + was[d2] >= V[u].size() )) { // should work
                     unhit_neighbors[d2] += !hit[d];
                     neighbors[d2]++;
                     // if ( neighbors[d2] == V[u].size() && unhit_neighbors[d2] == unhit && !hit[d2] ) {
                     if ( !was[d2] && neighbors[d2] == V[u].size() && unhit_neighbors[d2] == unhit && !hit[d2] ) {
                         dominates[d2].push_back(u);
                     }
                 }
             }

             for (int d : V[u]) was[d] = neighbors[d] = unhit_neighbors[d] = 0;
             for (int d : V[u]) for (int d2 : V[d]) neighbors[d2] = unhit_neighbors[d2] = 0;
         }

         for ( int i=0; i<N; i++ ) REMCVAL( hit, dominates[i] );

         VI U, N1, N2;
         VB in_U(N);
         VB in_N1(N);
         VB in_N2(N);
         VI temp; temp.reserve(10);

         constexpr int MAX_DEG = 10;

         if( !timer.tle(prepr_opt) )
         for ( int v=0; v<N; v++ ) if ( dominates[v].size() >= 2 && V[v].size() <= MAX_DEG ) {
             int max_deg_in_N1 = 0;
             for ( int d : V[v] ) max_deg_in_N1 = max(max_deg_in_N1, (int)V[d].size());
             if (max_deg_in_N1 > MAX_DEG) continue;
             if(++iter % TIMER_CHECK <= 1 ) if(timer.tle(prepr_opt)) break;

             U.clear(); in_U[v] = true; U.push_back(v);
             N1.clear();

             for (int d : V[v]){ in_N1[d] = true; N1.push_back(d); }


             for ( int u : dominates[v] ) if ( !in_N1[u] ) { // only dominated nodes nonadjacent to v are in U
                 in_U[u] = true;
                 U.push_back(u);
             }

             VI X;
             temp.clear();
             N2.clear();
             for ( int d : N1 ) { // creating closed neighborhood N2[v]
                 if (!was[d]) { was[d] = true; N2.push_back(d); }
                 for ( int dd : V[d] ) if (!was[dd]) { was[dd] = true; N2.push_back(dd); }
             }
             for (int d : N2) was[d] = false;
             for (int d : N2) in_N2[d] = true;

             int N2_unhit_size = 0;
             for (int d : N2) N2_unhit_size += !hit[d];

             auto isUDominatedByX = [&]() {
                 temp.clear();
                 for (int d : X) {
                     if (in_U[d] && !was[d]) { was[d] = true; temp.push_back(d); }
                     for (int dd : V[d]) if (in_U[dd] && !was[dd]) { was[dd] = true; temp.push_back(dd); }
                 }
                 assert(temp.size() <= U.size());
                 bool r = ( temp.size() == U.size() );
                 for (int d : temp) was[d] = false;
                 return r;
             };

             auto isN2UnhitDominatedByX = [&]() {
                 temp.clear();
                 for (int d : X) {
                     if (!was[d] && in_N2[d]) { was[d] = true; temp.push_back(d); }
                     for (int dd : V[d]) if (in_N2[dd] && !was[dd]) { was[dd] = true; temp.push_back(dd); }
                 }
                 int cnt = 0;
                 for ( int d : temp ) cnt += !hit[d];
                 for ( int d : temp) was[d] = false;
                 return cnt == N2_unhit_size;
             };

             if ( U.size() >= 3 && N2_unhit_size <= 3*MAX_DEG+3 ) {
                 // DEBUG(v); DEBUG(U);
                 VI sol;

                 bool found_prospective_X = false;
                 bool found_valid_X = false;

                 for ( int a : N1 ) if ( a != v ) {
                     X.clear(); X.push_back(a);
                     if ( isUDominatedByX() ) {
                         found_prospective_X = true;
                         if ( isN2UnhitDominatedByX() ) {
                             found_valid_X = true;
                             sol.push_back(a);
                             break;
                         }
                     }
                 }

                 // here, if domination_n123 rule was used before, such X={a} should not exists,
                 // since otherwise it would be removed by the rule

                 if ( !found_prospective_X ) {
                     // clog << "There is no single node in N1, that hit U: " << U << endl;
                     // clog << "\tN2.size(): " << N2.size() << ", N2_unhit_size: " << N2_unhit_size << endl;
                     for ( int i=0; i<N1.size(); i++){
                         for ( int j=i+1; j<N1.size(); j++ ) {
                             int a = N1[i], b = N1[j];
                             X.clear(); X.push_back(a); X.push_back(b);
                             if ( isUDominatedByX() ) {
                                 // clog << "\tPair of nodes {" << a << "," << b << "} dominates U!" << endl;
                                 found_prospective_X = true;
                                 if ( isN2UnhitDominatedByX() ) {
                                     found_valid_X = true;
                                     sol.push_back(a);
                                     sol.push_back(b);
                                     break;
                                 }
                             }
                         }
                         if ( found_valid_X ) break;
                     }
                 }

                 if ( !found_prospective_X && MAX_DEG <= 10 ) { // coonsider three nodes at once...
                     // clog << "There is no single node in N1, that hit U: " << U << endl;
                     // clog << "\tN2.size(): " << N2.size() << ", N2_unhit_size: " << N2_unhit_size << endl;
                     for ( int i=0; i<N1.size(); i++){
                         for ( int j=i+1; j<N1.size(); j++ ) {
                             for (int k=j+1; k<N1.size(); k++) {
                                 int a = N1[i], b = N1[j], c = N1[k];
                                 X.clear(); X.push_back(a); X.push_back(b); X.push_back(c);
                                 if ( isUDominatedByX() ) {
                                     // clog << "\tPair of nodes {" << a << "," << b << "} dominates U!" << endl;
                                     found_prospective_X = true;
                                     if ( isN2UnhitDominatedByX() ) {
                                         found_valid_X = true;
                                         sol.push_back(a);
                                         sol.push_back(b);
                                         sol.push_back(c);
                                         break;
                                     }
                                 }
                             }
                            if ( found_valid_X ) break;
                         }
                         if ( found_valid_X ) break;
                     }
                 }

                 assert( found_valid_X == !sol.empty() );
                 assert(sol.size() <= 3);
                 if (found_valid_X) {

                     // clog << "Found valid X for domination 4!, sol.size(): " << sol.size() << endl;
                     // {
                     //     clog << "Found valid X for domination 4!" << endl;
                     //     DEBUG(v);
                     //     DEBUG(U);
                     //     DEBUG(N1);
                     //     DEBUG(N2);
                     //     DEBUG(sol);
                     //     for (int d : N1) DEBUGV(V,d);
                     //     exit(5);
                     // }

                     domination_rules4_applied++;
                     changes = true;
                     for (int d : N2) hit[d] = true;

                     for ( int d : sol ) {
                         to_lift.push_back( new ReducibleRule(d) );
                         kernel.push_back(d); in_kernel[d] = true;
                     }

                     for (int d : N1) GraphUtils::removeNodeFromGraph(V,d);
                 }
             }


             // for (int d : U) in_U[d] = false;
             // for (int d : N1) in_N1[d] = false;
             // for (int d : N2) in_N2[d] = false;
             for (int d : N2) in_U[d] = in_N1[d] = in_N2[d] = false;
             U.clear();
             N1.clear();
             N2.clear();
         }

         if constexpr (make_measurements) timer.stop("domination_rules4_applied");

         if constexpr (write_logs_and_stats && make_measurements) {
             DEBUG(iter);
             DEBUG(timer.getTime("domination_rules4_applied") / 1000);
         }
    };

    auto path_rules = [&]() {
        if constexpr (make_measurements) timer.start("path_rules_applied");
        VI path; path.reserve(N);
        map<int,int> paths_sizes;
        VB removed(N);

        for( int v=0; v<N; v++ ) {
            // if( V[v].size() <= 2 ) continue;
            if( V[v].size() <= 1 || ( V[v].size() == 2 && !hit[v] ) ) continue;

            VI NEIGH = V[v];
            // for( int d : NEIGH ) { // original
            for( int d : NEIGH ) if ( V[d].size() == 2 && !hit[d] && !removed[d] ) { // this should be faster and do the same
                // if(removed[d]) continue;
                if( V[v].size() <= 1 ) break;

                assert(d != v);
                int u = d, prev = v;
                path.clear();
                path.push_back(v);
                // while( V[u].size() == 2 ) {
                // while( V[u].size() == 2 && u != v ) { // original
                while( V[u].size() == 2 && u != v && !hit[u] ) { // #TEST -contraction of 'hit-partitioned paths'
                    path.push_back(u);
                    if( V[u][0] == prev ) {
                        prev = u;
                        u = V[u][1];
                    }else {
                        prev = u;
                        u = V[u][0];
                    }
                    // if(u == v) {
                    //     path.clear();
                    //     break;
                    // }
                }
                path.push_back(u);
                // if(path.size() <= 2 || V[u].size() == 1 || u == v) continue;
                if(path.size() <= 2 || V[u].size() == 1) continue;

                // if constexpr (make_measurements)
                    paths_sizes[path.size()]++;

                // if all internal nodes on the path are unhit...
                bool internal_nodes_hit = false;
                for( int i=1; i+1 < path.size(); i++ ) internal_nodes_hit |= hit[path[i]];
                if(internal_nodes_hit) continue;


                int a = path[0], b = path.back();
                int internal_nodes_cnt = (int)path.size()-2;

                assert(a == v);
                assert( V[a].size() >= 2 );
                assert( V[b].size() >= 2 );

                if( a == b ) { // we have a cycle in which node a has perhaps degree > 2
                    // continue;
                    assert(internal_nodes_cnt > 1);
                    // if( !hit[a] && ((internal_nodes_cnt % 3) > 0) ) { // original

                    changes = true;
                    path_rules_applied++;

                    if( (internal_nodes_cnt % 3) > 0 ) { // #TEST - check if this works!!
                        // assert(false && "Cycle of length 3k+{1,2} can be 'removed', check if this works");
                        kernel.push_back(a);
                        to_lift.push_back( new ReducibleRule(a) );
                        hit[a] = true;
                        for(int dd : V[a]) hit[dd] = true;
                        GraphUtils::removeNodeFromGraph(V,a);
                        break; // a = b = v is taken, so we need to break here
                    }
                    else {
                        for( int i=2; i<path.size(); i += 3 ) {
                            int w = path[i];
                            hit[w] = hit[V[w][0]] = hit[V[w][1]] = true;
                            removed[w] = removed[V[w][0]] = removed[V[w][1]] = true;
                            kernel.push_back(w);
                            to_lift.push_back( new ReducibleRule(w) );
                        }
                        for( int i=2; i<path.size(); i += 3 ) GraphUtils::removeNodeFromGraph(V, path[i]);
                        continue;
                    }
                }

                if( hit[a] && hit[b] && ((internal_nodes_cnt % 3) == 0) ) {
                    // // if( V[a].size() == 2 || V[b].size() == 2 ) { // this happens in stress tests
                    // if( V[a].size() == 2 && V[b].size() == 2 ) { // this happens in stress tests
                    //     exit(6);
                    // }
                    changes = true;
                    for( int i=2; i+1 < path.size(); i+=3 ) {
                        to_lift.push_back( new ReducibleRule(path[i]) );
                        kernel.push_back(path[i]);
                        hit[path[i]] = true;
                        for( int dd : V[path[i]] ) hit[dd] = true;
                    }
                    for( int i=1; i+1<path.size(); i++ ) {
                        GraphUtils::removeNodeFromGraph(V, path[i]);
                        removed[path[i]] = true;
                    }
                    if constexpr( write_logs_and_stats ) clog << "Found reducible path instance, "
                            "both ends are hit and there are 3k internal nodes" << endl;
                    path_rules_applied++;
                    // assert(false && "This assertion is only for check if this situation happens, remove it later");
                }
                else if( path.size() >= 5 ) { // this should work normally, if not for the bug...
                    changes = true;

                    VI short_path;
                    int len = (internal_nodes_cnt % 3);
                    short_path.reserve(len+2);
                    short_path.push_back(a);
                    for( int i=1; i<=len; i++ ) short_path.push_back(path[i]);
                    short_path.push_back(b);

                    // DEBUG(path);
                    // DEBUG(short_path);
                    // exit(2);
                    VPII lpn(path.size());
                    for( int i=0; i<path.size(); i++ ) lpn[i] = { V[path[i]][0], V[path[i]][1] };

                    for( int i=1; i+1<path.size(); i++ ) assert(V[path[i]].size() == 2);
                    for( int i=1; i+1<path.size(); i++ ) {
                        GraphUtils::removeNodeFromGraph(V, path[i]);
                        removed[path[i]] = true;
                    }
                    VI va = V[a], vb = V[b];
                    for( int i=1; i<short_path.size(); i++ ) {
                        // do not add edge, if it already exists...
                        if( short_path.size() == 2 && StandardUtils::find(V[a],b) ) continue;
                        GraphUtils::addEdge(V, short_path[i-1], short_path[i]);
                    }

                    // assert(V[a].size() >= 3);
                    // assert(V[b].size() >= 3);

                    // to_lift.push_back( new PathRule(short_path, path, va,vb) );
                    auto * rule = new PathRule(short_path, path, va,vb, lpn);
                    tie( rule->is_a_hit, rule->is_b_hit ) = PII{hit[a], hit[b]};
                    to_lift.push_back( rule );
                    path_rules_applied++;
                }
            }
        }
        // if constexpr (write_logs_and_stats && make_measurements) if(!paths_sizes.empty())
        if constexpr (enable_logs)
            if (recursive_reductions_level == 0) DEBUG(paths_sizes);
        if constexpr (make_measurements) timer.stop("path_rules_applied");
    };

    auto path_rules23 = [&]() {
        if constexpr (make_measurements) timer.start("path_rules2&3_applied");
        VI path; path.reserve(N);
        VVI path_lengths(N);
        VVI path1_internal_nodes(N);
        VI temp;

        constexpr bool use_hit_path2_condition = false; // this seems to work, but does not bring any overall benefit
        VI temp2;
        vector<pair<bool,bool>> path_lengths2_hit_types;
        if constexpr (use_hit_path2_condition) {
            path_lengths2_hit_types = vector<pair<bool,bool>>(N, {false,false});
        }

        for( int v=0; v<N; v++ ) {
            if( V[v].size() <= 2 ) continue;
            // if(hit[v]) continue;

            temp.clear();
            temp2.clear();

            // for( int d : V[v] ) { // original
            for( int d : V[v] ) if ( V[d].size() == 2 ) {
                if( V[v].size() <= 2 ) break;

                int u = d, prev = v;
                path.clear();
                path.push_back(v);
                while( V[u].size() == 2 && u != v ) {
                    path.push_back(u);
                    if( V[u][0] == prev ) {
                        prev = u;
                        u = V[u][1];
                    }else {
                        prev = u;
                        u = V[u][0];
                    }
                }
                path.push_back(u);
                if(path.size() <= 2 || V[u].size() == 1 || u == v) continue;
                // if(hit[u]) continue;
                // if(hit[u] && hit[v]) continue; // nope
                // if((hit[u] || hit[v]) && ( !hit[u] || !hit[v] )) continue; // if only one belongs...

                bool internal_nodes_hit = false;
                for( int i=1; i+1 < path.size(); i++ ) internal_nodes_hit |= hit[path[i]];
                if(internal_nodes_hit) {
                    if constexpr (use_hit_path2_condition) if( path.size() == 4 ){
                        int a = path[0], b = path.back();
                        int x = path[1], y = path[2];
                        if( hit[x] && !hit[y] ) {
                            path_lengths2_hit_types[b].first = true;
                            temp2.push_back(b);
                        }
                        if( !hit[x] && hit[y] ) {
                            path_lengths2_hit_types[b].second = true;
                            temp2.push_back(b);
                        }
                    }
                    continue;
                }

                int a = path[0], b = path.back();
                assert(V[b].size() >= 3);
                assert(a == v && b != v);
                int internal_nodes_cnt = (int)path.size()-2;
                assert( internal_nodes_cnt >= 1 );
                assert( internal_nodes_cnt <= 2 && "This should hold if path compression was applied earlier" );
                temp.push_back(b);
                path_lengths[b].push_back(internal_nodes_cnt);
                if( internal_nodes_cnt == 1 ) path1_internal_nodes[b].push_back( path[1] );
            }

            bool can_both_ends_be_added = false;
            int second_end = -1;
            for( int b : temp ) {
                bool contains_2 = false;
                for( int dd : path_lengths[b] ) contains_2 |= (dd == 2);
                bool cond = (contains_2 && (path_lengths[b].size() >= 2));
                if constexpr ( use_hit_path2_condition ) {
                    cond |= (contains_2 && (path_lengths2_hit_types[b].first || path_lengths2_hit_types[b].second));
                }
                if( cond ) {
                    can_both_ends_be_added = true;
                    second_end = b;
                    assert(v != b);
                }
            }
            if constexpr (use_hit_path2_condition) if(!can_both_ends_be_added) {
                // StandardUtils::makeUnique(temp2);
                for(int b : temp2) if(b != v) {
                    bool c = ( path_lengths2_hit_types[b].first && path_lengths2_hit_types[b].second );
                    if(c) {
                        can_both_ends_be_added = true;
                        second_end = b;
                        clog << endl << "use_hit_path2_condition applied" << endl << endl;
                    }
                    if(can_both_ends_be_added) break;
                }
            }

            if(can_both_ends_be_added) {
                path_rules2_applied++;
                changes = true;

                kernel.push_back(v);
                kernel.push_back(second_end);
                to_lift.push_back( new ReducibleRule(v) );
                to_lift.push_back( new ReducibleRule(second_end) );
                assert(second_end != -1 && second_end != v);
                hit[v] = hit[second_end] = true;
                for( int d : V[v] ) hit[d] = true;
                for( int d : V[second_end] ) hit[d] = true;
                GraphUtils::removeNodeFromGraph(V, v);
                GraphUtils::removeNodeFromGraph(V, second_end);
            }else if(true) {
                for( int i=(int)temp.size()-1; i>=0; i-- ) { // equivalent to makeUnique()
                    if(was[temp[i]]){ REM(temp,i); }
                    else was[temp[i]] = true;
                }
                for(int d : temp) was[d] = false;


                auto Vv = V[v];
                for(int d : V[v]) was[d] = true; was[v] = true;
                for( int b : temp ) { // original
                    if constexpr (!use_hit_path2_condition) if( path1_internal_nodes[b].size() <= 1 ) continue;
                    if constexpr (use_hit_path2_condition) if( path1_internal_nodes[b].empty() ||
                        ( (path1_internal_nodes[b].size() == 1) &&
                            !path_lengths2_hit_types[b].first && !path_lengths2_hit_types[b].second ) ) continue;

                    assert(b != v);
                    for( int d : path1_internal_nodes[b] ) assert(!hit[d]);
                    for( int d : path1_internal_nodes[b] ) helper[d] = true;
                    bool has_common_unhit_intersection = ( (was[b] && (!hit[b] || !hit[v]) ) );
                    if (has_common_unhit_intersection) path_rules3_applied_value_4++;
                    if(has_common_unhit_intersection) hit[b] = hit[v] = true;
                    bool bb0 = has_common_unhit_intersection;
                    bool bb = false;
                    for( int d : V[b] ) if( d != v && was[d] && !helper[d] && !hit[d] ) {
                        has_common_unhit_intersection = true;
                        bb = true;
                        hit[d] = true;
                        if constexpr( write_logs_and_stats ) clog << "\tMarking node " << d << " as hit" << endl;
                    }
                    if (!bb0 && bb) path_rules3_applied_value_5++;

                    if constexpr (use_rules_for_excluded)
                    if( has_common_unhit_intersection ) for( int d : path1_internal_nodes[b] ) excluded[d] = true;

                    if (path1_internal_nodes[b].size() > 2) {
                        if (!has_common_unhit_intersection) path_rules3_applied_value_3++;
                        has_common_unhit_intersection = true;
                        for ( int i=2; i<path1_internal_nodes[b].size(); i++ ) {
                            int d = path1_internal_nodes[b][i];
                            hit[d] = true;
                            changes = true;
                            GraphUtils::removeNodeFromGraph(V,d);
                            if constexpr( write_logs_and_stats )
                                clog << "Path rule - removing node " << d << " from graph" << endl;
                        }
                    }

                    if(has_common_unhit_intersection) {
                        // int switch_to = b;
                        for( int d : path1_internal_nodes[b] ) {
                            // to_lift.push_back(new DomRed(d,switch_to) );
                            to_lift.push_back(new DomRedPath(d,{v,b}) );
                            path_rules3_applied_value_2++;
                            // if constexpr( write_logs_and_stats )
                            //     clog << "Adding path-3 DomRedPath -> swap " << d << " to " << switch_to << endl;
                            // if ( switch_to == v ) switch_to = b;
                            // else switch_to = v;
                        }
                        if constexpr( write_logs_and_stats ) clog << "\tpath3 rule applied" << endl;
                        changes = true;
                        path_rules3_applied++;
                    }
                    for( int d : path1_internal_nodes[b] ) helper[d] = false;

                }
                // for(int b : temp) for( int d : path1_internal_nodes[b] ) helper[d] = false;
                // for(int d : V[v]) was[d] =  false; was[v] = false; // if v was removed from graph... ?
                for(int d : Vv) was[d] =  false; was[v] = false;
            }

            for(int b : temp2) path_lengths2_hit_types[b] = {false,false};
            for(int b : temp) path_lengths[b].clear();
            for(int b : temp) path1_internal_nodes[b].clear();
            temp.clear();
        }
        if constexpr (make_measurements) timer.stop("path_rules2&3_applied");
    };

    auto domination_n123_2nodes = [&]() {
        if constexpr (make_measurements) timer.start("domination_n123_2nodes_rules_applied");
        if constexpr( write_logs_and_stats ) clog << "Starting 2n_dom reduction" << endl;

        VI perm(N);
        // VI cnt(N,0);
        VI dst(N,inf);
        VI neigh_cnt(N,0);
        iota(ALL(perm),0);
        sort(ALL(perm), [&]( int a, int b ){ return V[a].size() > V[b].size(); });
        VI neigh_uv, to_remove, N3_nodes, N3_unhit_nodes;
        VB N1(N), N2(N), N3(N);
        VB N1UH(N);
        VB was2(N);

        // constexpr int MAX_DEG = 10;
        constexpr int MAX_DEG = 20;
        constexpr int MAX_NEIGHUV_SIZE = 30;

        int iter = 0;

        for( int u : perm ) {
            if( V[u].empty() ) continue;
            if( V[u].size() > MAX_DEG ) continue;
            if(++iter % 8 == 0 ) if(timer.tle(prepr_opt)) break;

            VI NEIGH = findReachableNodesFromSWithinDistanceK( V, {u}, 3, dst, helper );

            for( int v : NEIGH ) if( v < u ) {
                if( V[v].size() > MAX_DEG ) continue;

                neigh_uv.clear();
                to_remove.clear();
                bool applied_gadget = false;

                for( int d : V[u] ) if( !was[d] ) { was[d] = true; neigh_uv.push_back(d); }
                for( int d : V[v] ) if( !was[d] ) { was[d] = true; neigh_uv.push_back(d); }

                if(neigh_uv.size() > MAX_NEIGHUV_SIZE) { for(int d : neigh_uv) was[d] = false; continue; }


                constexpr bool use_uhe_version = true; // this works, but causes a roughly 10% incrase to prepr. time
                // constexpr bool use_uhe_version = use_lossy_rules_for_excluded; // this works, but causes a roughly 10% incrase to prepr. time

                for( int w : neigh_uv ) {
                    bool temp = false;
                    bool temp2 = false;
                    for( int d : V[w] ) {
                        temp |= (d != u && d != v && !was[d] ); // original
                        if constexpr (!use_uhe_version) if(temp) break; // not breaking is faster in practice
                        if constexpr (use_uhe_version) {
                            temp2 |= (d != u && d != v && !was[d] && !hit[d] ); // original
                        }
                    }
                    if(temp) N1[w] = true;
                    if constexpr (use_uhe_version) if(temp2) N1UH[w] = true;
                }

                for(int d : neigh_uv) was[d] = false;

                N3_nodes.clear();
                N3_unhit_nodes.clear();
                bool has_N3_unhit = 0;
                int N3_unhit_cnt = 0;

                for( int w : neigh_uv ) { // here we only check if there exists
                    if( N1[w] ) continue;
                    bool has_n1_neighbor = false;
                    if constexpr (!use_uhe_version) for( int dd : V[w] ) has_n1_neighbor |= N1[dd];
                    else {
                        bool has_n1_uhe_neighbor = false;
                        for( int dd : V[w] ) {
                            checkAndUnmarkExcludedNode(dd);
                            has_n1_uhe_neighbor |= N1UH[dd] && !excluded[dd];
                        }
                        has_n1_neighbor = has_n1_uhe_neighbor;
                    }

                    has_N3_unhit |= !hit[w] && !has_n1_neighbor;
                    if(!hit[w] && !has_n1_neighbor) break;
                }

                if(has_N3_unhit) {
                    for( int w : neigh_uv ) {
                        if( N1[w] ) continue;
                        bool has_n1_neighbor = false;
                        if constexpr (!use_uhe_version) for( int dd : V[w] ) has_n1_neighbor |= N1[dd];
                        else {
                            bool has_n1_uhe_neighbor = false;
                            for( int dd : V[w] ) {
                                checkAndUnmarkExcludedNode(dd);
                                has_n1_uhe_neighbor |= N1UH[dd] && !excluded[dd];
                            }
                            has_n1_neighbor = has_n1_uhe_neighbor;
                        }

                        if(has_n1_neighbor) N2[w] = true;
                        else {
                            N3_unhit_cnt += !hit[w];
                            if(!hit[w]) N3_unhit_nodes.push_back(w);
                            N3[w] = true;
                            N3_nodes.push_back(w);
                        }
                    }
                }


                if( N3_unhit_cnt > 0 ) { // original
                    bool can_be_dominated_by_single_node = false;
                    for( int d : N3_unhit_nodes ) {
                        neigh_cnt[d]++;
                        if( neigh_cnt[d] == N3_unhit_cnt ) {
                            can_be_dominated_by_single_node = true;
                            break;
                        }

                        // constexpr bool admit_single_node_domination_and_gadget_case = true; // #TEST - set to false to use 'standard' version
                        // constexpr bool admit_single_node_domination_and_gadget_case = false;
                        constexpr bool admit_single_node_domination_and_gadget_case = use_lossy_rules_for_excluded;
                        for( int d2 : V[d] ) {
                            if constexpr (admit_single_node_domination_and_gadget_case) if( d2 == u || d2 == v ) continue;
                            neigh_cnt[d2]++;
                            if( neigh_cnt[d2] == N3_unhit_cnt ) {
                                can_be_dominated_by_single_node = true;
                                break;
                            }
                        }
                        if(can_be_dominated_by_single_node) break;
                    }

                    if( !can_be_dominated_by_single_node ) {
                        // int temp = 0;
                        int temp = ( N3[u] && !hit[u] );
                        for( int d : V[u] ) temp += ( N3[d] && !hit[d] );
                        bool N3_unhit_dominated_by_u = ( temp >= N3_unhit_cnt );
                        if(N3_unhit_dominated_by_u) assert(temp == N3_unhit_cnt);

                        // temp = 0;
                        temp = ( N3[v] && !hit[v] );
                        for( int d : V[v] ) temp += ( N3[d] && !hit[d] );
                        bool N3_unhit_dominated_by_v = ( temp >= N3_unhit_cnt );
                        if(N3_unhit_dominated_by_v) assert(temp == N3_unhit_cnt);

                        auto addGadget = [&](int a, int b) {
                            // assert(false && "gadget not tested yet, as it seems to never occur...");
                            // DEBUG(PII(a,b)); DEBUGV(V,a); DEBUGV(V,b); DEBUGV(V,u); DEBUGV(V,v);
                            // clog << "N1: "; for( int d : neigh_uv ) if( N1[d] ) clog << d << " "; clog << endl;
                            // clog << "N2: "; for( int d : neigh_uv ) if( N2[d] ) clog << d << " "; clog << endl;
                            // clog << "N3: "; for( int d : neigh_uv ) if( N3[d] ) clog << d << " "; clog << endl;
                            // DEBUG(N3_unhit_nodes);

                            hit[a] = hit[b] = false;
                            excluded[a] = excluded[b] = false;
                            was[a] = N1[a] = N2[a] = N3[a] = N1UH[a] = false;
                            was[b] = N1[b] = N2[b] = N3[b] = N1UH[b] = false;
                            neigh_cnt[a] = neigh_cnt[b] = 0;

                            GraphUtils::removeNodeFromGraph(V,a);
                            GraphUtils::removeNodeFromGraph(V,b);
                            GraphUtils::addEdge(V,u,a);
                            GraphUtils::addEdge(V,u,b);
                            GraphUtils::addEdge(V,v,a);
                            GraphUtils::addEdge(V,v,b);
                            bool adj = false;
                            for( int d : V[u] ) adj |= (d == v);
                            to_lift.push_back( new DomRed2( {a,b}, {u,v}, adj ) );
                            if constexpr (use_rules_for_excluded) excluded[a] = excluded[b] = true;
                        };

                        auto gadgetCase = [&](int min_neigh) {
                            bool gadget_added = false;

                            for( int d : V[u] ) was2[d] = true;
                            for( int d : V[v] ) helper[d] = true;
                            for( auto w : neigh_uv ) if( w != u && w != v && !N1[w] ) {
                                // if( N3[w] ) to_remove.push_back(w);
                                if( N3[w] || ( N2[w] && was2[w] && helper[w] ) ) to_remove.push_back(w); // original
                                // if( (N3[w] || N2[w]) && was2[w] && helper[w]  ) to_remove.push_back(w); // worse
                                // if( N3[w] && was2[w] && helper[w]  ) to_remove.push_back(w); //worsest :)
                                // if( N3[w] && was2[w] && helper[w] && !hit[w] ) to_remove.push_back(w); //more worsest...
                            }
                            for( int d : V[u] ) was2[d] = false;
                            for( int d : V[v] ) helper[d] = false;

                            int a = -1, b = -1;
                            if( to_remove.size() >= min_neigh ) {
                                a = to_remove.back();
                                to_remove.pop_back();
                                b = to_remove.back();
                                to_remove.pop_back();

                                bool are_to_remove_already_gadget_nodes = ( V[a].size() == 2 && V[b].size() == 2 && to_remove.empty() ); // #TEST
                                if(  !are_to_remove_already_gadget_nodes ) {
                                    addGadget(a,b);
                                    gadget_added = true;
                                }

                            }else to_remove.clear();


                            if(gadget_added){
                                for( int d : V[u] ) was2[d] = true;
                                for( int d : V[v] ) helper[d] = true;
                                for( auto w : neigh_uv ) {
                                    if( w != a && w != b )
                                        if( w != u && w != v && was2[w] && helper[w]  ) hit[w] = true;
                                }
                                for( int d : V[u] ) was2[d] = false;
                                for( int d : V[v] ) helper[d] = false;
                            }

                            return gadget_added;
                        };

                        if( N3_unhit_dominated_by_u || N3_unhit_dominated_by_v ) {
                            // assert(false && "This if should be in another 'else' section, because v cannot be dominated by sinble node " );

                            if( N3_unhit_dominated_by_u && N3_unhit_dominated_by_v ) {
                                // clog << "Gadget case 1! This is not tested properly yet!!!" << endl;
                                // applied_gadget |= gadgetCase(3); // original
                                applied_gadget = false; // #TEST
                                // if(applied_gadget) assert(false && "Gadget case 1! This is not tested properly yet!!!");
                                // clog << "Condition N3_unhit_dominated_by_u && N3_unhit_dominated_by_v met!" << endl;
                                if(applied_gadget) changes = true;
                            }
                            else if( N3_unhit_dominated_by_u ) {
                                // assert(false && "Case 1");
                                assert(!N3_unhit_dominated_by_v);
                                kernel.push_back(u); in_kernel[u] = true;
                                to_lift.push_back( new ReducibleRule(u) );
                                hit[u] = true;
                                for(int d : V[u]) hit[d] = true;
                                changes = true;

                                to_remove.push_back(u);
                            }
                            else if( N3_unhit_dominated_by_v ) {
                                // assert(false && "Case 2");
                                assert(!N3_unhit_dominated_by_u);
                                kernel.push_back(v); in_kernel[v] = true;
                                to_lift.push_back( new ReducibleRule(v) );
                                hit[v] = true;
                                for(int d : V[v]) hit[d] = true;
                                changes = true;

                                to_remove.push_back(v);
                            }
                        }

                        else {
                            temp = N3[u];
                            // for( int d : V[u] ) if( N3[d] ) temp++;
                            for( int d : V[u] ) temp += N3[d];
                            bool N3_dominated_by_u = ( temp >= N3_nodes.size());
                            if(N3_dominated_by_u) assert(temp == N3_nodes.size());

                            temp = N3[v];
                            // for( int d : V[v] ) if( N3[d] ) temp++;
                            for( int d : V[v] ) temp += N3[d];
                            bool N3_dominated_by_v = ( temp >= N3_nodes.size() );
                            if(N3_dominated_by_v) assert(temp == N3_nodes.size());

                            // if( !N3_dominated_by_u && !N3_dominated_by_v ) { // this should be valid...
                            if( !N3_unhit_dominated_by_u && !N3_unhit_dominated_by_v ) {
                                // {
                                //     DEBUG(u); DEBUGV(hit,u); DEBUGV(excluded,u);
                                //     DEBUGV(V,u); DEBUG(N3_unhit_dominated_by_u);
                                //     DEBUG(v); DEBUGV(hit,v); DEBUGV(excluded,v);
                                //     DEBUGV(V,v); DEBUG(N3_unhit_dominated_by_v);
                                //     DEBUG(N3_nodes); DEBUG(N3_unhit_nodes);
                                //     for(int d : N3_nodes) DEBUGV(N3,d);
                                //     for(int d : neigh_uv) { DEBUGV(V,d); DEBUGV(hit,d); DEBUGV(excluded,d); }
                                //     exit(1);
                                // }
                                kernel.push_back(u);
                                to_lift.push_back( new ReducibleRule(u) );
                                kernel.push_back(v);
                                to_lift.push_back( new ReducibleRule(v) );
                                changes = true;

                                hit[u] = hit[v] = true;
                                for( int w : neigh_uv ) hit[w] = true;
                                for( int w : neigh_uv ) if(N2[w] || N3[w]) to_remove.push_back(w);
                                to_remove.push_back(u);
                                to_remove.push_back(v);
                            }
                        }
                    }
                }

                was[u] = N1[u] = N2[u] = N3[u] = was[v] = N1[v] = N2[v] = N3[v] = N1UH[v] = false;
                for( int d : V[u] ) was[d] = N1[d] = N2[d] = N3[d] = N1UH[d] = false;
                for( int d : V[v] ) was[d] = N1[d] = N2[d] = N3[d] = N1UH[d] = false;
                neigh_cnt[u] = neigh_cnt[v] = 0;
                for( int d : V[u] ) neigh_cnt[d] = 0;
                for( int d : V[v] ) neigh_cnt[d] = 0;

                if(!to_remove.empty() || applied_gadget) break;
            }

            for( int d : to_remove ) GraphUtils::removeNodeFromGraph(V,d);
            domination_n123_2nodes_rules_applied += (!to_remove.empty());
            changes |= !to_remove.empty();

        }// u loop
        if constexpr (make_measurements) timer.stop("domination_n123_2nodes_rules_applied");
    };

    auto art_point_rules = [&]() {
        if constexpr (make_measurements) timer.start("art_point_rules_applied");

        auto markCC = [&]( int v, int start, VB & vis, VI & cc, int max_size ) {
            vis[v] = true;
            cc.push_back(start);
            vis[start] = true;
            for( int i=0; i<cc.size(); i++ ) {
                for( int d : V[cc[i]] ) if(!vis[d]) {
                    vis[d] = true;
                    cc.push_back(d);
                    if( cc.size() > max_size ) return false; // safer, as it might break iterating over all neighbors
                }
                if( cc.size() > max_size ) return false; // original
            }
            return true;
        };


        auto considerCC = [&](int v, VI & cc ) {
            for( int d : cc ) was[d] = true;

            int unhit_cnt = 0;
            for(int d : cc) unhit_cnt += !hit[d];

            int res = 0;

            if(unhit_cnt > 0) {

                int unhit_covered_by_v = 0;
                for(int d : V[v]) unhit_covered_by_v += ( was[d] && !hit[d]);
                assert(unhit_cnt >= unhit_covered_by_v);

                if( unhit_covered_by_v == unhit_cnt ) { // if v covers all unhit nodes in cc
                    // we can add v to the solution
                    if constexpr( write_logs_and_stats ) {
                        clog << "Art-point rule applied, we can add v: " << v << " to the solution" << endl;
                        DEBUG(v); DEBUGV(V,v); DEBUG(cc);
                        for( int d : cc ) DEBUGV(V,d);
                        for( int d : cc ) DEBUGV(hit,d);
                    }

                    kernel.push_back(v);
                    to_lift.push_back( new ReducibleRule(v) );
                    for(int d : V[v]) hit[d] = true; hit[v] = true;
                    GraphUtils::removeNodeFromGraph(V, v);
                    res = 1;
                }else { // if v does not cover all nodes...
                    for(int d : V[v]) helper[d] = true;
                    int dominator = -1;
                    for( int d : cc ) {
                        int temp = !hit[d];
                        for( int d2 : V[d] ) temp += ( was[d2] && !hit[d2] );
                        if( (temp == unhit_cnt) && ( dominator == -1 || !helper[dominator] ) ) dominator = d;
                        // if( (temp == unhit_cnt) && ( dominator == -1 || helper[d] ) ) dominator = d; // logically 'equivalent'
                    }
                    for(int d : V[v]) helper[d] = false;

                    if( dominator != -1 ) { // if there exists a node in cc that covers all unhit nodes in cc

                        if constexpr( write_logs_and_stats ) {
                            clog << "Art-point rule applied, we can add dominator: "
                                 << dominator << " to the solution" << endl;
                            DEBUG(v); DEBUGV(V,v); DEBUG(cc); DEBUG(dominator);
                            for( int d : cc ) DEBUGV(V,d);
                            for( int d : cc ) DEBUGV(hit,d);
                        }

                        for( int d : V[dominator] ) hit[d] = true; hit[dominator] = true;
                        kernel.push_back(dominator);
                        to_lift.push_back( new ReducibleRule(dominator) );
                        GraphUtils::removeNodeFromGraph(V, dominator);
                        res = 2;
                    }else{
                        for(int d : V[v]) helper[d] = true;

                        int unhit_nonv_neigh = 0;
                        for(int d : cc) unhit_nonv_neigh += (!hit[d] && !helper[d]);

                        int semi_dominator = -1;
                        for( int d : cc ){
                            int temp = (!hit[d] && !helper[d]);
                            for(int d2 : V[d]) temp += ( was[d2] && !hit[d2] && !helper[d2] );
                            assert( temp <= unhit_nonv_neigh );
                            if( temp == unhit_nonv_neigh ){ semi_dominator = d; break; }
                        }

                        for(int d : V[v]) helper[d] = false;

                        if( semi_dominator != -1 ){
                            if constexpr( write_logs_and_stats ) {
                                clog << "Art-point rule applied, we can add semi-dominator: "
                                     << semi_dominator << " and v: " << v << " to the solution" << endl;
                                DEBUG(v); DEBUGV(V,v); DEBUG(cc); DEBUG(semi_dominator);
                                for( int d : cc ) DEBUGV(V,d);
                                for( int d : cc ) DEBUGV(hit,d);
                            }

                            for( int d : V[semi_dominator] ) hit[d] = true; hit[semi_dominator] = true;
                            kernel.push_back(semi_dominator);
                            to_lift.push_back( new ReducibleRule(semi_dominator) );
                            GraphUtils::removeNodeFromGraph(V, semi_dominator);

                            for( int d : V[v] ) hit[d] = true; hit[v] = true;
                            kernel.push_back(v);
                            to_lift.push_back( new ReducibleRule(v) );
                            GraphUtils::removeNodeFromGraph(V, v);

                            res = 3;
                        }
                    }
                }
            }

            for( int d : cc ) was[d] = false;

            return res;
        };

        VI vis_all; vis_all.reserve(N);
        VI cc;
        VB vis(N);

        auto [art_points, bridges] = BridgesAndArtPoints::getBridgesAndArtPoints(V);

        double avg_deg = 0;
        {
            int c = 0;
            for( int i=0; i<N; i++ ){ avg_deg += V[i].size(); c += !V[i].empty();}
            avg_deg /= c+1;
            avg_deg += 3;
        }

        int iter = 0;
        for(int v : art_points) {
            if( iter++ % 32 == 0 ) if( timer.tle(prepr_opt) ) break;

            vis_all.clear();
            for( int u : V[v] ) {
                if( vis[u] ) continue;

                cc.clear();
                int max_size = max( V[v].size(), V[u].size() ) + 2*avg_deg;
                max_size = min( max_size, 20 ); // original
                auto consider = markCC( v, u, vis, cc, max_size );
                vis_all += cc;
                if( cc.size() > max_size ) {
                    for(int d : cc) vis[d] = false;
                    vis[v] = false;
                    continue;
                }

                int r = 0;
                if(consider) r = considerCC(v, cc);
                changes |= (r > 0);
                art_point_rules_applied += (r > 0);
                if(r) break;
            }

            for(int d : vis_all) vis[d] = false;
            vis[v] = false;
        }
        if constexpr (make_measurements) timer.stop("art_point_rules_applied");
    };

    constexpr bool use_initial_rules = false;
    if(use_initial_rules) if(!timer.tle(prepr_opt)) {
        if constexpr (make_measurements) timer.start("initial_basic_and_path");
        basic_rules();
        path_rules();
        basic_rules();
        path_rules23();
        if constexpr (make_measurements) timer.stop("initial_basic_and_path");
    }

    auto funnel_folding = [&]() {

        if constexpr (make_measurements) timer.start("funnel_folding_rules_applied");

        auto inducesClique = [&](VI & zb)-> bool {
            if (zb.empty()) return true;
            int cnt = 0;
            for ( int d : zb ) was[d] = true;
            for (int d : zb) {
                int c = 0;
                for ( int dd : V[d] ) c += was[dd];
                if ( c != zb.size()-1 ) break;
                cnt += c;
            }
            for ( int d : zb ) was[d] = false;
            return cnt == (zb.size() * (zb.size()-1));
        };

        VPII to_add;

        auto applyFunnel = [&]( int v, int a, int b, VI & A, VI & B, const bool add_antiedges = true ) {
            VI to_remove = {a,b,v};
            for (int d : to_remove) GraphUtils::removeNodeFromGraph(V, d);
            to_lift.push_back( new FunnelFolding(v,a,b,A,B) );
            to_add.clear();

            if (add_antiedges) {
                for ( int d : A ) {
                    for ( int dd : V[d] ) was[dd] = true;
                    for ( int dd : B ) if ( !was[dd] && !( hit[d] && hit[dd] ) && !(excluded[d] && excluded[dd]) ) {
                        // if (d != dd) GraphUtils::addEdge(V,d,dd);
                        if (d != dd) to_add.emplace_back(min(d,dd), max(d,dd));
                    }
                    for ( int dd : V[d] ) was[dd] = false;
                }

                StandardUtils::makeUnique(to_add);
                for (auto [d,dd] : to_add) GraphUtils::addEdge(V,d,dd);
            }
        };

        constexpr int MAX_DEG = 7;
        int iter = 0;

        VI A,B;

        for( int v=0; v<N; v++ ) if( V[v].size() == 2 && !hit[v] ) {
            if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;

            int a = V[v][0], b = V[v][1];
            if( hit[a] || hit[b] ) continue; // this condition is absolutely necessary

            if ( V[a].size() > MAX_DEG || V[b].size() > MAX_DEG ) continue;
            // if ( StandardUtils::find(V[a],b) ) continue; // this is most probably not necessary

            A.clear();
            B.clear();

            for ( int d : V[a] ) if (d != v) A.push_back(d);
            for ( int d : V[b] ) if (d != v) B.push_back(d);

            bool has_A_unhit_node = false;
            for (int d : A) has_A_unhit_node |= !hit[d];
            bool has_B_unhit_node = false;
            for (int d : B) has_B_unhit_node |= !hit[d];
            // if (!has_A_unhit_node || !has_B_unhit_node) continue; // this is most probably not necessary

            bool has_common_intersection = false;
            for ( int d : A ) was[d] = true;
            for (int d : B ) has_common_intersection |= was[d];
            for ( int d : A ) was[d] = false;
            if (has_common_intersection) continue; // this is necessary

            if ( !inducesClique(A) || !inducesClique(B) ) continue;

            // clog << "Applying funnel to v: " << v << ", a: " << a << ", b: " << b
            // << ", A: " << A << ", B: " << B << endl;

            applyFunnel(v,a,b,A,B);
            funnel_folding_rules_applied++;
            changes = true;
        }
        if constexpr (make_measurements) timer.stop("funnel_folding_rules_applied");
    };


    constexpr bool remove_additional_nodes_in_funnels_on_the_spot = false;
    bool recent_funnel_rule_changes = false;

     auto funnel3_nonfolding = [&]() {

         recent_funnel_rule_changes = false;

        auto inducesClique = [&](VI & zb)-> bool {
            if (zb.empty()) return true;
            int cnt = 0;
            for ( int d : zb ) was[d] = true;
            for (int d : zb) {
                int c = 0;
                for ( int dd : V[d] ) c += was[dd];
                if ( c != zb.size()-1 ) break;
                cnt += c;
            }
            for ( int d : zb ) was[d] = false;
            return cnt == (zb.size() * (zb.size()-1));
        };

         // constexpr bool admit_common_AB_intersection = false;

         auto isFullBipartite = [&](VI & A, VI & B) {
             if ( A.empty() || B.empty() ) return true;
             for( int d : B ) was[d] = true;
             bool is_full_bipartite = true;
             for(int a : A) {
                 int cnt = 0;
                 // if constexpr (admit_common_AB_intersection) if( was[a] ) cnt = 1;
                 for( int d : V[a] ) cnt += was[d];
                 is_full_bipartite &= (cnt == B.size());
                 if(!is_full_bipartite) break;
             }
             for( int d : B ) was[d] = false;
             return is_full_bipartite;
         };

        VPII to_add;

        constexpr int MAX_DEG = 5;
        int iter = 0;

        if constexpr (make_measurements) timer.start("funnel3_nonfolding_rules_applied");
        VI A,B,B1,B2;

        for( int v=0; v<N; v++ ) if( V[v].size() == 2 && !hit[v] ) {
            if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;

            int a = V[v][0], b = V[v][1];
            if( !hit[a] || hit[b] ) swap(a,b); // this condition is absolutely necessary
            if( !hit[a] || hit[b] ) continue; // this condition is absolutely necessary

            if ( V[a].size() > MAX_DEG || V[b].size() > MAX_DEG ) continue;
            if ( V[a].size() == 1 || V[b].size() == 1 ) continue;
            // if ( StandardUtils::find(V[a],b) ) continue; // this is most probably not necessary

            A.clear();
            B.clear();
            B1.clear(); B2.clear();

            for ( int d : V[a] ) if (d != v) A.push_back(d);
            for ( int d : V[b] ) if (d != v) B.push_back(d);
            for ( int d : V[b] ) if (d != v ){ if (!hit[d]) B1.push_back(d); else B2.push_back(d); }

            bool has_A_unhit_node = false;
            for (int d : A) has_A_unhit_node |= !hit[d];
            bool has_B_unhit_node = false;
            for (int d : B) has_B_unhit_node |= !hit[d];
            // if (!has_A_unhit_node || !has_B_unhit_node) continue; // this is most probably not necessary
            // if (!has_A_unhit_node) continue; // this is most probably not necessary
            if (!has_B_unhit_node) continue; // this is most probably not necessary

            // if constexpr (!admit_common_AB_intersection) {
                bool has_common_intersection = false;
                for ( int d : A ) was[d] = true;
                for (int d : B ) has_common_intersection |= was[d];
                for ( int d : A ) was[d] = false;
                if (has_common_intersection) continue; // this is necessary? // this condition is necessary
            // }

            // if ( !inducesClique(B) ) continue; // original
            if ( !inducesClique(B1) || !isFullBipartite(B1,B2) ) continue; // #TEST - seems to work ok
            if ( !isFullBipartite(A,B) ) continue;

            // clog << "Applying funnel3 to v: " << v << ", a: " << a << ", b: " << b
            // << ", A: " << A << ", B: " << B << endl;

            {
                kernel.push_back(b);
                in_kernel[b] = true;
                to_lift.push_back(new ReducibleRule(b));
                hit[b] = true;
                for(int d : V[b]) hit[d] = true;
                GraphUtils::removeNodeFromGraph(V,b);
                if constexpr(remove_additional_nodes_in_funnels_on_the_spot)
                    if( A.size() >= 2 || ( A.size() == 1 && V[A[0]].size() >= 2 ) )
                    GraphUtils::removeNodeFromGraph(V,a); // we can also immediately remove a...
                {
                    // we could also remove all edges from the clique B...
                    for(int d : B) was[d] = true;
                    int cur = 0;
                    for(int d : B) cur += V[d].size();
                    for(int d : B) REMCVAL(was, V[d]);
                    int cur2 = 0;
                    for(int d : B) cur2 += V[d].size();
                    assert(((cur2-cur) & 1) == 0);
                    hit_edges_removed += ( cur2 - cur ) / 2;
                    for(int d : B) was[d] = false;
                }
            }
            funnel3_nonfolding_rules_applied++;
            changes = true;
            recent_funnel_rule_changes = true;
        }
        if constexpr (make_measurements) timer.stop("funnel3_nonfolding_rules_applied");
    };


    auto small_connected_components = [&]() {

        if constexpr (make_measurements) timer.start("small_conn_comps_rules_applied");

        constexpr bool consider_only_cycles = true;

        VI res1, res2;
        auto dsseForCycleWithHitNode = [&]( auto & V, VB hit ) -> VI {
            int v = -1;
            for(int i=0; i<V.size(); i++) if(hit[i]) v = i;
            assert(v != -1); assert(hit[v]);
            res1.clear(); res2.clear();
            for(auto & v : V) assert(v.size() == 2);

            {
                auto W = V;
                auto hit2 = hit;
                for(int d : W[v]) hit2[d] = true;
                GraphUtils::removeNodeFromGraph(W,v);
                DSReducer red(hit2);
                red.recursive_reductions_level = 1;
                auto [ker,h,e,penud,lft] = red.reductionRulesDS(W, inf, true);
                for(auto & w : W) assert(w.empty()); // graph should be empty after basic reductions
                VB res(V.size());
                for(auto * r : lft) {
                    r->lift(res);
                    delete r;
                }
                res1 = StandardUtils::toVI(res);
                res1.push_back(v);
                assert(DSS::isCorrect(V,res1,1,hit));
            }

            {
                auto W = V;
                auto hit2 = hit;
                // for(int d : V[v]) hit2[d] = true; // we select not to add v to the solution
                GraphUtils::removeNodeFromGraph(W,v);
                DSReducer red(hit2);
                red.recursive_reductions_level = 1;
                auto [ker,h,e,penud,lft] = red.reductionRulesDS(W, inf, true);
                for(auto & w : W) assert(w.empty()); // graph should be empty after basic reductions
                VB res(V.size());
                for(auto * r : lft) {
                    r->lift(res);
                    delete r;
                }
                res2 = StandardUtils::toVI(res);
                assert(DSS::isCorrect(V,res2,1,hit));
            }

            if( res1.size() <= res2.size() ) return res1;
            else return res2;
        };

        auto findOptimalDS = [&](VVI & V, VB hit, VB exc) -> VI {
            if constexpr (consider_only_cycles) return dsseForCycleWithHitNode(V,hit);

            DSSE dsse(V,hit,exc);
            if( V.size() > 15 ) dsse.exact_hs_solving_method = MILP;
            else dsse.exact_hs_solving_method = NONE; // use branching for small graphs...
            if constexpr (consider_only_cycles) dsse.exact_hs_solving_method = NONE;
            return dsse.solve();
        };

        // constexpr int MAX_COMP_SIZE = 50;
        constexpr int MAX_COMP_SIZE = (consider_only_cycles ? 200 : 30);
        // constexpr int MAX_RES_SIZE_TO_CHECK = 4;
        VI cyc;
        cyc.reserve(MAX_COMP_SIZE);

        auto comps = ConnectedComponents::getConnectedComponents(V);
        sort(ALL(comps), [&]( auto & v1, auto & v2 ){ return v1.size() < v2.size(); });
        // clog << "Running small connected components rule, comps.size(): " << comps.size() << endl;

        for ( auto & cmp : comps ) if (cmp.size() > 1 && cmp.size() <= MAX_COMP_SIZE) {

            InducedGraph g = GraphInducer::induce(V,cmp);
            bool is_cycle = GraphUtils::isCycle(g.V);
            bool hit_nodes_cnt = 0;
            for (int d : g.nodes) hit_nodes_cnt += hit[d];

            // if (is_cycle && hit_nodes_cnt <= 1) {
            if (is_cycle && hit_nodes_cnt == 0) { //#CAUTION this seems to be incorrect
                small_conn_comp_considered++;

                int hn = -1;
                int beg = 0;
                for ( int i=0; i<g.V.size(); i++ ) if ( hit[g.nodes[i]] ) {
                    beg = (i+2) % g.nodes.size();
                    hn = beg;
                }

                if ( hit_nodes_cnt == 1 ) assert( hit[g.nodes[(beg + g.V.size() - 2) % g.V.size()]] );

                { // remove just a single node and let basic_rules() do the rest
                    beg = g.nodes[beg];
                    hit[beg] = true;
                    for (int d : V[beg]) hit[d] = true;
                    to_lift.push_back( new ReducibleRule(beg) );
                    GraphUtils::removeNodeFromGraph(V,beg);
                    continue;
                }

                // // clog << endl << "Starting removing nodes on cycle with node " << beg
                //      // << ", hit[" << beg << "]: " << hit[g.nodes[beg]] << endl;
                //
                // int u = beg, v = g.V[u][0];
                // cyc.clear();
                // cyc.push_back(u);
                // while ( v != beg ) {
                //     cyc.push_back(v);
                //     int w = ( g.V[v][0] == u ? g.V[v][1] : g.V[v][0] );
                //     u = v;
                //     v = w;
                // }
                //
                // // clog << "Found a cycle with at most one hit node - removing every third node" << endl;
                // // DEBUG(cyc);
                //
                // for (int & d : cyc) d = g.nodes[d];
                // for ( int i=0; i<cyc.size(); i+=3 ) {
                //     int v = cyc[i];
                //     kernel.push_back(v);
                //     in_kernel[v] = true;
                //     // clog << "Removing node " << g.perm[v] << endl;
                //     to_lift.push_back( new ReducibleRule(v) );
                //     hit[v] = true;
                //     for (int d : V[v]) hit[d] = true;
                //     GraphUtils::removeNodeFromGraph(V,v);
                // }
                //
                // for ( int d : cyc ) if (!hit[d]) {
                //     in_kernel[d] = true;
                //     to_lift.push_back( new ReducibleRule(d) );
                //     hit[d] = true;
                //     for (int dd : V[d]) hit[dd] = true;
                //     GraphUtils::removeNodeFromGraph(V,d);
                // }
                //
                // continue;
            }

            if constexpr (consider_only_cycles) if(!is_cycle) continue; // with this we consider only cycle-components
            // if(timer.tle(prepr_opt)) continue;
            if constexpr (!consider_only_cycles) if(timer.tle(prepr_opt)) continue;

            if(recursive_reductions_level == 0) {
                small_conn_comp_considered++;
                changes = true;
                VB hit_nodes_g(g.V.size());
                VB excluded_nodes_g(g.V.size());
                for ( int i=0; i<g.V.size(); i++ ) hit_nodes_g[i] = hit[g.nodes[i]];
                for ( int i=0; i<g.V.size(); i++ ) excluded_nodes_g[i] = excluded[g.nodes[i]];
                VI opt = findOptimalDS(g.V, hit_nodes_g, excluded_nodes_g );
                g.remapNodes(opt);
                for (int v : opt) {
                    kernel.push_back(v);
                    in_kernel[v] = true;
                    to_lift.push_back( new ReducibleRule(v) );
                    hit[v] = true;
                    for (int d : V[v]) hit[d] = true;
                    GraphUtils::removeNodeFromGraph(V,v);
                }
            }
        }

        if constexpr (make_measurements) timer.stop("small_conn_comps_rules_applied");
    };

    auto funnel2_nonfolding = [&]() {

        if constexpr (make_measurements) timer.start("funnel2_nonfolding_applied");

        recent_funnel_rule_changes = false;

        constexpr int MAX_DEG_AB = 20;
        constexpr int MAX_DEG_W = 100;
        VI A,B;
        VI neigh_cnt(N,0);

        for ( int u = 0; u<N; u++ ) if ( V[u].size() == 2 && !hit[u] ) {
            int a = V[u][0], v = V[u][1];
            if ( V[a].size() != 2 && V[v].size() != 2 ) continue;
            if ( V[v].size() != 2 ) swap(a,v);
            assert(V[v].size() == 2);

            int b = V[v][0];
            if (b == u) b = V[v][1];
            if ( V[a].size() > MAX_DEG_AB || V[b].size() > MAX_DEG_AB ) continue;
            if ( hit[a] || hit[b] || hit[u] || hit[v] ) continue;
            if ( StandardUtils::find(V[a],b) ) continue;

            A.clear();
            B.clear();
            for (int d : V[a]) if (d != u) A.push_back(d);
            for (int d : V[b]) if (d != v) B.push_back(d);

            bool has_common_intersection = false;
            for (int d : A) was[d] = true;
            for ( int d : B ) has_common_intersection |= was[d];
            for (int d : A) was[d] = false;
            if (has_common_intersection) continue;

            bool exists_dominator = false;
            int dominator = -1;
            VI AB = A+B;
            for (int d : AB) was[d] = true;
            for ( int d : AB ) {
                neigh_cnt[d]++;
                if ( V[d].size() <= MAX_DEG_W ) for ( int dd : V[d] ) neigh_cnt[d] += was[dd];
                exists_dominator |= ( neigh_cnt[d] == A.size() + B.size() );
                neigh_cnt[d] = 0;
                if (exists_dominator && ( dominator == -1 || hit[dominator] ) ) {
                    dominator = d;
                    break;
                }
            }
            for (int d : AB) was[d] = false;

            if ( exists_dominator && (!hit[dominator] || ((!excluded[a] || !excluded[b]) && use_rules_for_excluded) ) ) {
            // if ( exists_dominator ) {
                excluded[a] = excluded[b] = true;
                hit[dominator] = true;

                to_lift.push_back( new Funnel2Nonfolding(u,v,a,b,A,B, dominator) );
                funnel2_nonfolding_applied++;
                changes = true;
                recent_funnel_rule_changes = true;

                // clog << "Applying funnel2_nonfolding rule, a: " << a << ", u: " << u <<
                //     ", v: " << v << ", b: " << b << endl;
                // { // marking as hit also all other nodes that dominate A+B
                //     for ( int d : AB ) neigh_cnt[d]++;
                //     for ( int d : AB ) for ( int dd : V[d] ) if (dd != a && dd != b) {
                //         neigh_cnt[dd]++;
                //         if (neigh_cnt[dd] == A.size() + B.size()) {
                //             clog << "Applying funnel2_nonfolding to a (possibly auxiliary) dominator dd: " << dd << endl;
                //             DEBUG(dd);
                //             DEBUG(dominator);
                //             hit[dd] = true;
                //         }
                //     }
                //     for ( int d : AB ) neigh_cnt[d] = 0;
                //     for ( int d : AB ) for ( int dd : V[d] ) neigh_cnt[dd] = 0;
                // }
                // DEBUGV(V,a);
                // DEBUGV(V,b);
                // DEBUG(dominator);
                // DEBUGV(V,dominator);
                // exit(3);
            }
        }

        if constexpr (make_measurements) timer.stop("funnel2_nonfolding_applied");
    };

     auto funnel4_nonfolding = [&]() {
        if constexpr (make_measurements) timer.start("funnel4_nonfolding_applied");

         recent_funnel_rule_changes = false;

         auto inducesClique = [&](VI & zb)-> bool {
             if (zb.empty()) return true;
             int cnt = 0;
             for ( int d : zb ) was[d] = true;
             for (int d : zb) {
                 int c = 0;
                 for ( int dd : V[d] ) c += was[dd];
                 if ( c != zb.size()-1 ) break;
                 cnt += c;
             }
             for ( int d : zb ) was[d] = false;
             return cnt == (zb.size() * (zb.size()-1));
         };

         auto isFullBipartite = [&](VI & A, VI & B) {
             if ( A.empty() || B.empty() ) return true;
             for( int d : B ) was[d] = true;
             bool is_full_bipartite = true;
             for(int a : A) {
                 int cnt = 0;
                 for( int d : V[a] ) cnt += was[d];
                 is_full_bipartite &= (cnt == B.size());
                 if(!is_full_bipartite) break;
             }
             for( int d : B ) was[d] = false;
             return is_full_bipartite;
         };

        constexpr int MAX_DEG = 6;
        VI A,B,B1,B2;
        VI neigh_cnt(N,0);

        for ( int u = 0; u<N; u++ ) if ( V[u].size() == 2 && !hit[u] ) {
            int a = V[u][0], v = V[u][1];
            if ( V[a].size() != 2 && V[v].size() != 2 ) continue;
            if ( V[v].size() != 2 ) swap(a,v);
            assert(V[v].size() == 2);

            int b = V[v][0];
            if (b == u) b = V[v][1];
            if( V[a].size() == 1 || V[b].size() == 1 ) continue;
            if ( V[a].size() > MAX_DEG || V[b].size() > MAX_DEG ) continue;
            if ( !hit[a] || hit[u] || !hit[v] || hit[b] ) continue;
            if ( StandardUtils::find(V[a],b) ) continue;

            A.clear(); B.clear(); B1.clear(); B2.clear();
            for (int d : V[a]) if (d != u) A.push_back(d);
            for (int d : V[b]) if (d != v) B.push_back(d);
            for (int d : V[b]) if (d != v ){ if (!hit[d]) B1.push_back(d); else B2.push_back(d); }

            bool has_common_intersection = false;
            for (int d : A) was[d] = true;
            for ( int d : B ) has_common_intersection |= was[d];
            for (int d : A) was[d] = false;
            if (has_common_intersection) continue;

            // if( !inducesClique(B) ) continue; // original
            // if( !isFullBipartite(A,B) ) continue; // original

            if (!admit_heuristic_rules){ // #TEST - this seems to work ok, needs more tests
                if( !inducesClique(B1) ) continue; // original
                if( !isFullBipartite(B1,B2) ) continue; // original
                if( !isFullBipartite(A,B) ) continue; // original
            }

            if (admit_heuristic_rules){ // #TEST funnel4 similar to funnel5 - seems to produce WA for some tests
                int dominator = -1;
                for (int d : B1) was[d] = true;
                VI AB1 = A+B1;
                for ( int d : AB1 ) neigh_cnt[d] = 1;
                for ( int d : AB1 ) {
                    for ( int dd : V[d] ) if (was[dd]) {
                        neigh_cnt[dd]++;
                        if ( neigh_cnt[dd] == AB1.size() ) {
                            dominator = dd;
                            break;
                        }
                    }
                    if (dominator != -1) break;
                }

                for (int d : B1) was[d] = false;
                for ( int d : AB1 ) neigh_cnt[d] = 0; // clearing
                for ( int d : AB1 ) for ( int dd : V[d] ) neigh_cnt[dd] = 0;  // clearing
                if (dominator == -1) continue;
            }

            {
                // clog << "Applying funnel4_nonfolding rule, a: " << a << ", u: " << u <<
                // ", v: " << v << ", b: " << b << endl;
                // DEBUGV(V,a); DEBUGV(V,b); for(int d : B) DEBUGV(V,d); exit(3);

                hit[v] = hit[u] = hit[b] = true;
                in_kernel[v] = true;
                kernel.push_back(v);
                to_lift.push_back(new ReducibleRule(v));
                GraphUtils::removeNodeFromGraph(V,v);
                if constexpr(remove_additional_nodes_in_funnels_on_the_spot)
                    if( A.size() >= 1 )
                    GraphUtils::removeNodeFromGraph(V,u); // u can also be removed
                if constexpr(remove_additional_nodes_in_funnels_on_the_spot)
                    if( B.size() >= 2 || ( B.size() == 1 && V[B[0]].size() >= 2 ) )
                    GraphUtils::removeNodeFromGraph(V,b); // b can also be removed
                funnel4_nonfolding_applied++;
                changes = true;
                recent_funnel_rule_changes = true;
            }
        }

        if constexpr (make_measurements) timer.stop("funnel4_nonfolding_applied");
    };


    auto funnel5_nonfolding = [&]() {

        if constexpr (make_measurements) timer.start("funnel5_nonfolding_applied");

        recent_funnel_rule_changes = false;

        constexpr int MAX_DEG = 10;
        VI A,B1,B2;
        VI neigh_cnt(N,0);
        int iter = 0;

        for ( int u = 0; u<N; u++ ) if ( V[u].size() == 2 && !hit[u] ) {
            int a = V[u][0], v = V[u][1];
            if ( V[a].size() != 2 && V[v].size() != 2 ) continue;
            if ( V[v].size() != 2 ) swap(a,v);
            assert(V[v].size() == 2);

            int b = V[v][0];
            if (b == u) b = V[v][1];
            if( V[a].size() == 1 || V[b].size() == 1 ) continue;
            if ( V[a].size() > MAX_DEG || V[b].size() > MAX_DEG ) continue;
            if ( !hit[a] || hit[u] || hit[v] || hit[b] ) continue;
            // if ( StandardUtils::find(V[a],b) ) continue;

            if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;

            A.clear(); B1.clear(); B2.clear();
            for (int d : V[a]) if (d != u) A.push_back(d);
            for (int d : V[b]) if (d != v) {
                if ( !hit[d] ) B1.push_back(d);
                else B2.push_back(d);
            }

            bool has_common_intersection = false;
            for (int d : A) was[d] = true;
            for ( int d : B1 ) has_common_intersection |= was[d];
            for (int d : A) was[d] = false;
            // if (has_common_intersection) continue;

            int dominator = -1;
            VI AB1 = A+B1;
            for ( int d : AB1 ) neigh_cnt[d] = 1;
            for ( int d : AB1 ) {
                for ( int dd : V[d] ) {
                    neigh_cnt[dd]++;
                    if ( neigh_cnt[dd] == AB1.size() ) {
                        dominator = dd;
                        break;
                    }
                }
                if (dominator != -1) break;
            }

            for ( int d : AB1 ) neigh_cnt[d] = 0; // clearing
            for ( int d : AB1 ) for ( int dd : V[d] ) neigh_cnt[dd] = 0;  // clearing

            if ( dominator != -1 ) {
                // {
                //     clog << "Applying funnel5_nonfolding rule, a: " << a << ", u: " << u <<
                //     ", v: " << v << ", b: " << b << endl;
                //     DEBUG(A); DEBUG(B1); DEBUG(B2);
                //     DEBUG(dominator);
                //     DEBUGV(V,a); DEBUGV(V,b); DEBUGV(V,dominator);
                //     exit(3);
                // }

                to_lift.push_back( new ReducibleRule(v) );
                kernel.push_back(v);
                in_kernel[v] = true;
                hit[u] = hit[v] = hit[b] = true;
                GraphUtils::removeNodeFromGraph(V,v);
                was[b] = true;
                hit_edges_removed += B2.size();
                for (int d : B2) REMCVAL(was,V[d]);
                was[b] = false;
                funnel5_nonfolding_applied++;
                changes = true;
                recent_funnel_rule_changes = true;
            }
        }

        if constexpr (make_measurements) timer.stop("funnel5_nonfolding_applied");
    };


    auto funnel6_nonfolding = [&]() {
        if constexpr (make_measurements) timer.start("funnel6_nonfolding_applied");

        recent_funnel_rule_changes = false;

        constexpr int MAX_DEG = 10;
        VI A,B;
        VI neigh_cnt(N,0);
        int iter = 0;

        for ( int u = 0; u<N; u++ ) if ( V[u].size() == 2 && !hit[u] ) {
            int a = V[u][0], v = V[u][1];
            if ( V[a].size() != 2 && V[v].size() != 2 ) continue;
            if ( V[v].size() != 2 ) swap(a,v);
            assert(V[v].size() == 2);

            int b = V[v][0];
            if (b == u) b = V[v][1];
            if( V[a].size() == 1 || V[b].size() == 1 ) continue;
            if ( V[a].size() > MAX_DEG || V[b].size() > MAX_DEG ) continue;
            if ( !hit[a] || hit[u] || hit[v] || !hit[b] ) continue;

            if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;

            A.clear(); B.clear();
            for (int d : V[a]) if (d != u) A.push_back(d);
            for (int d : V[b]) if (d != v) B.push_back(d);

            bool has_common_intersection = false;
            for (int d : A) was[d] = true;
            for ( int d : B ) has_common_intersection |= was[d];
            for (int d : A) was[d] = false;
            // if (has_common_intersection) continue; // #TEST is it necessary??


            int dominator = -1;
            VI AB = A+B;
            for ( int d : AB ) neigh_cnt[d] = 1;
            for ( int d : AB ) {
                for ( int dd : V[d] ) if (dd != a && dd != b) {
                // for ( int dd : V[d] ) {
                    neigh_cnt[dd]++;
                    if ( neigh_cnt[dd] == AB.size() ) {
                        dominator = dd;
                        break;
                    }
                }
                if (dominator != -1) break;
            }

            for ( int d : AB ) neigh_cnt[d] = 0; // clearing
            for ( int d : AB ) for ( int dd : V[d] ) neigh_cnt[dd] = 0;  // clearing

            if ( dominator != -1 ) {
                // {
                //     clog << "Applying funnel6_nonfolding rule, a: " << a << ", u: " << u <<
                //     ", v: " << v << ", b: " << b << endl;
                //     DEBUG(A); DEBUG(B); DEBUG(dominator);
                //     DEBUGV(V,a); DEBUGV(V,b); DEBUGV(V,dominator);
                //     exit(3);
                // }

                to_lift.push_back( new ReducibleRule(v) ); // add u or v, it does not matter which one
                kernel.push_back(v);
                in_kernel[v] = true;
                hit[u] = hit[v] = true;
                GraphUtils::removeNodeFromGraph(V,v);

                if constexpr(remove_additional_nodes_in_funnels_on_the_spot)
                    if( A.size() >= 2 || ( A.size() == 1 && V[A[0]].size() >= 2) )
                    GraphUtils::removeNodeFromGraph(V,a);
                if constexpr(remove_additional_nodes_in_funnels_on_the_spot)
                    if( A.size() >= 1 )
                    GraphUtils::removeNodeFromGraph(V,u);
                if constexpr(remove_additional_nodes_in_funnels_on_the_spot)
                    if( B.size() >= 2 || ( B.size() == 1 && V[B[0]].size() >= 2 ) )
                    GraphUtils::removeNodeFromGraph(V,b);

                funnel6_nonfolding_applied++;
                changes = true;
                recent_funnel_rule_changes = true;
            }
        }

        if constexpr (make_measurements) timer.stop("funnel6_nonfolding_applied");
    };

     auto funnel7_nonfolding = [&]() {

        if constexpr (make_measurements) timer.start("funnel7_nonfolding_applied");

         recent_funnel_rule_changes = false;

        constexpr int MAX_DEG = 7;
        VI A,B;
        VI neigh_cnt(N,0);
        int iter = 0;

        for ( int v=0; v<N; v++ ) if ( V[v].size() == 2 && hit[v] ) {

            int u = V[v][0], w = V[v][1];
            if ( V[u].size() != 2 || V[w].size() != 2 ) continue;
            if (hit[u] || hit[w]) continue;

            int a = (V[u][0] == v ? V[u][1] : V[u][0]);
            int b = (V[w][0] == v ? V[w][1] : V[w][0]);

            if (!hit[a] || !hit[b]) continue;
            if ( V[a].size() > MAX_DEG || V[b].size() > MAX_DEG ) continue;

            if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;

            A.clear(); B.clear();
            for (int d : V[a]) if (d != u) A.push_back(d);
            for (int d : V[b]) if (d != w) B.push_back(d);

            if (A.empty() || B.empty()) continue;

            // bool has_common_intersection = false;
            // for (int d : A) was[d] = true;
            // for ( int d : B ) has_common_intersection |= was[d];
            // for (int d : A) was[d] = false;
            // if (has_common_intersection) continue; // #TEST is it necessary??

            int dominator = -1;
            VI AB = A+B;
            for ( int d : AB ) neigh_cnt[d] = 1;
            for ( int d : AB ) {
                for ( int dd : V[d] ) if (dd != a && dd != b) {
                    neigh_cnt[dd]++;
                    if ( neigh_cnt[dd] == AB.size() ) {
                        dominator = dd;
                        break;
                    }
                }
                if (dominator != -1) break;
            }

            for ( int d : AB ) neigh_cnt[d] = 0; // clearing
            for ( int d : AB ) for ( int dd : V[d] ) neigh_cnt[dd] = 0;  // clearing

            if ( dominator != -1 ) {
                // {
                //     clog << "Applying funnel7_nonfolding rule, a: " << a << ", u: " << u <<
                //     ", v: " << v << ", w: " << w << ", b: " << b << endl;
                //     DEBUG(A); DEBUG(B); DEBUG(dominator);
                //     DEBUGV(V,a); DEBUGV(V,u); DEBUGV(V,v); DEBUGV(V,b); DEBUGV(V,dominator);
                //     exit(3);
                // }

                to_lift.push_back( new ReducibleRule(v) ); // add u or v, it does not matter which one
                kernel.push_back(v);
                in_kernel[v] = true;
                hit[u] = hit[w] = true;
                GraphUtils::removeNodeFromGraph(V,v);
                GraphUtils::removeNodeFromGraph(V,u);
                GraphUtils::removeNodeFromGraph(V,w);

                funnel7_nonfolding_applied++;
                changes = true;
                recent_funnel_rule_changes = true;
            }
        }

        if constexpr (make_measurements) timer.stop("funnel7_nonfolding_applied");
    };


    auto excluded_domination = [&]() {
        if constexpr (!use_rules_for_excluded) return;

        if constexpr (make_measurements) timer.start("excluded_domination_applied");

        constexpr int MAX_DEG = 30; // cannot exceed 64
        VI mask(N,0); // integer type must contain at least MAX_DEG bits

        VI perm(N);
        iota(ALL(perm),0);
        int iter = 0;
        VI unhit_neighbors(N,0);
        VVI dominates(N);

        sort(ALL(perm), [&]( int a, int b ){ return V[a].size() < V[b].size(); });
        VB considered(N);
        VI neighbors(N,0);

        for (int u : perm) {
            if ( V[u].empty() || hit[u] ) continue; // u cannot be hit, as it would be removed using dom2
            if(++iter % TIMER_CHECK == 0 ) if(timer.tle(prepr_opt)) break;

            int unhit = 0;

            for ( int d : V[u]) unhit += !hit[d];
            if (unhit == 0) continue;

            for ( int d : V[u] ) {
                was[d] = true;
                unhit_neighbors[d] = !hit[d];
                neighbors[d] = 1;
            }
            for ( int d : V[u] ) {
                for ( int d2 : V[d] ) if (d2 != u) {
                    unhit_neighbors[d2] += !hit[d];
                    neighbors[d2]++;
                    if ( !was[d2] && neighbors[d2] == V[u].size() && unhit_neighbors[d2] == unhit && !hit[d2] ) {
                        dominates[d2].push_back(u);
                    }
                }
            }

            for (int d : V[u]) was[d] = neighbors[d] = unhit_neighbors[d] = 0;
            for (int d : V[u]) for (int d2 : V[d]) neighbors[d2] = unhit_neighbors[d2] = 0;
        }

        VI n2_nodes;
        n2_nodes.reserve(2*MAX_DEG);
        VB was2(N);

        reverse(ALL(perm)); // from smallest degree now

        for ( int v : perm ) if ( !dominates[v].empty() && V[v].size() <= MAX_DEG && !excluded[v] && !hit[v] ) {
            if(++iter % 16 == 0 ) if(timer.tle(prepr_opt)) break;
            // if ( hit[v] ) continue; // is it necessary?? probably not, as all such v will be hit... :)

            n2_nodes.clear();

            for (int d : V[v]) was[d] = true;

            int D = V[v].size();
            for ( int i=0; i<D; i++ ) {
                int d = V[v][i];
                if ( !was2[d] ) { was2[d] = true; n2_nodes.push_back(d); }
                mask[d] |= (1 << i);
                if ( V[d].size() <= MAX_DEG )  for ( int dd : V[d] ) if ( dd != v ) {
                    mask[dd] |= (1 << i);
                    if ( !was2[dd] ) { was2[dd] = true; n2_nodes.push_back(dd); }
                }
            }


            sort(ALL(n2_nodes), [&](int a, int b){ return V[a].size() > V[b].size(); });
            sort(ALL(dominates[v]), [&](int a, int b){ return V[a].size() < V[b].size(); });

            for ( int u : dominates[v] ) if (V[u].size() <= MAX_DEG && !was[u]) {
                if (hit[u]) continue; // #TEST is it necessary?

                bool for_each_neigh_of_u = true;
                bool all_neigh_excluded = true;
                for ( int d : V[u] ) {
                    bool exists_w_for_d = false;
                    // #CAUTION - check here by iterating over all nodes in n2_nodes might be time-consuming
                    // preprocessing for small MAX_DEG (e.g. 10) might make it possible to check in O(1) time for
                    // each d if there exists valid w, but preprocessing takes O(2^MAX_DEG) time
                    // for ( int w : n2_nodes ) if ( (mask[d] | mask[w]) == ((1<<D)-1) ) {
                    // for ( int w : n2_nodes ) if (w != u && !excluded[w] && !hit[w]) if ( (mask[d] | mask[w]) == ((1<<D)-1) ) {
                    for ( int w : n2_nodes ) if (w != u && !excluded[w]) if ( (mask[d] | mask[w]) == ((1<<D)-1) ) {
                    // for ( int w : n2_nodes ) if (!excluded[w] && !hit[w]) if ( (mask[d] | mask[w]) == ((1<<D)-1) ) {
                    // for ( int w : n2_nodes ) if (!excluded[w] && !hit[w] && w != u) if ( (mask[d] | mask[w]) == ((1<<D)-1) ) {
                        exists_w_for_d = true;
                        assert(w != v);
                        break;
                    }
                    for_each_neigh_of_u &= exists_w_for_d;
                    if (!for_each_neigh_of_u) break;
                    all_neigh_excluded &= excluded[d];
                }

                // if (for_each_neigh_of_u && !all_neigh_excluded) {
                //     clog << "Excluded domination applies!" << endl;
                //     DEBUG(v);
                //     DEBUG(u);
                //     DEBUGV(V,v);
                //     DEBUGV(V,u);
                //     DEBUG(n2_nodes);
                //     for ( int d : n2_nodes ) DEBUGV(V,d);
                //     ENDL(2);
                //
                //     for ( int d : V[u] ) {
                //         clog << "Considering neighbor d: " << d << " of u: " << u << endl;
                //         for ( int w : n2_nodes ) if ( (mask[d] | mask[w]) == ((1<<D)-1) ) {
                //             clog << "\tFound valid node w: " << w << endl;
                //             clog << "\t"; DEBUGV(excluded,w);
                //             clog << "\t"; DEBUGV(hit,w);
                //             // break;
                //         }
                //     }
                //
                //     // exit(2);
                // }


                // if (for_each_neigh_of_u) {
                if (for_each_neigh_of_u && !all_neigh_excluded) {
                    excluded[v] = true;
                    changes = true;
                    excluded_domination_applied++;
                    break;
                }
            }

            // clearing
            was[v] = was2[v] = mask[v] = 0;
            for (int d : V[v]) {
                was[d] = was2[d] = mask[d] = 0;
                // if ( V[d].size() <= MAX_DEG ) for ( int dd : V[d] ) was[dd] = was2[dd] = mask[dd] = 0;
                for (int dd : n2_nodes) was[dd] = was2[dd] = mask[dd] = 0;
            }

        }

        if constexpr (make_measurements) timer.stop("excluded_domination_applied");
    };





     auto recursive_reductions = [&]() {
        // return; // this rule does not work correctly yet...
        // if (recursive_reductions_level > 0) return;
        if (!use_recursive_reducer) return;

        if constexpr(write_logs_and_stats) clog << "Starting recursive reductions on level 0" << endl;

        if constexpr (make_measurements) timer.start("recursive_reducer");

        Stopwatch tmp_timer;

        auto createReducibleNodes = [&]( auto & reducibles, auto & lft ) {
            reducibles.clear();
            for ( auto * r : lft ) {
                if ( r->getName() == "reducible" ) {
                    auto rr = static_cast<ReducibleRule*>(r);
                    reducibles.push_back(rr->v);
                }
            }
        };

        VI perm(N);
        iota(ALL(perm),0);
        sort(ALL(perm), [&](int a, int b){ return V[a].size() < V[b].size(); });

         VI cnt(N,0);

         VVI reducibles(N);

        //  clog << "Running recursive reductions for each node in turn" << endl;
        //  for ( int v : perm ) if (!V[v].empty() && !excluded[v]) {
        //      if (timer.tle(prepr_opt)) break;
        //
        //      VVI W = V;
        //      auto ind_hit = hit;
        //      int w = v;
        //      ind_hit[w] = true;
        //      for (int d : V[w]) ind_hit[d] = true;
        //      GraphUtils::removeNodeFromGraph(W,w);
        //
        //      int time_left_millis = timer.getLimit(prepr_opt) - timer.getTime(prepr_opt);
        //      DSReducer dss_rec(ind_hit, excluded );
        //      dss_rec.recursive_reductions_level = recursive_reductions_level+1;
        //      auto [ker, hit, exc, lft ] =
        //          // dss_rec.reductionRulesDS(W,time_left_millis);
        //          dss_rec.reductionRulesDS(W,time_left_millis,true);
        //      lft.push_back(new ReducibleRule(w));
        //      createReducibleNodes(reducibles[v], lft);
        //      for (auto * r : lft) delete r;
        //  }
        //
        // for ( int v : perm ) if (!V[v].empty() && !excluded[v]) {
        //     if (timer.tle(prepr_opt)) break;
        //
        //     VI inters;
        //     VVI red; red.reserve(V[v].size()+1);
        //     red.push_back(reducibles[v]);
        //     for (int d : V[v]) if (!excluded[d]) red.push_back(reducibles[d]);
        //
        //     for ( auto & zb : red ) {
        //         for (int d : zb) {
        //             cnt[d]++;
        //             if (cnt[d] == red.size()) inters.push_back(d);
        //         }
        //     }
        //     for ( auto & zb : red ) for (int d : zb) cnt[d] = 0;
        //
        //     if ( !inters.empty() ) {
        //         clog << "Found recursively a set of reducible nodes: " << inters << endl;
        //         // exit(1);
        //     }
        // }


         clog << "Running recursive reductions" << endl;
         VB valid(N);

         for ( int v : perm ) if (!V[v].empty() ) {
             if (timer.tle(prepr_opt)) break;

             VI ZB = V[v];
             ZB.push_back(v);

             for ( int i=0; i<N; i++ ) checkAndUnmarkExcludedNode(i);

             bool cannot_find = false;
             for (int d : ZB) cannot_find |= (valid[d] && !excluded[d] && reducibles[d].empty());
             // for (int d : ZB) cannot_find |= (valid[d] && reducibles[d].empty());
             if (cannot_find) continue;


             auto exc = excluded;

             for (int w : ZB) if (!excluded[w] && !valid[w]) {
             // for (int w : ZB) if (!valid[w]) {
             // for (int w : ZB) {
                 VVI W = V;
                 auto ind_hit = hit;
                 ind_hit[w] = true;
                 for (int d : V[w]) ind_hit[d] = true;
                 GraphUtils::removeNodeFromGraph(W,w);

                 excluded = exc;
                 for ( int i=0; i<N; i++ ) checkAndUnmarkExcludedNode(i);

                 int time_left_millis = timer.getLimit(prepr_opt) - timer.getTime(prepr_opt);
                 DSReducer dss_rec(ind_hit, excluded );
                 // DSReducer dss_rec(ind_hit );
                 dss_rec.recursive_reductions_level = recursive_reductions_level+1;
                 auto [ker, h, exc, penud, lft ] =
                     // dss_rec.reductionRulesDS(W,time_left_millis);
                     dss_rec.reductionRulesDS(W,time_left_millis,false);
                 lft.push_back(new ReducibleRule(w));
                 createReducibleNodes(reducibles[w], lft);
                 valid[w] = true;
                 for (auto * r : lft) delete r;
             }

             excluded = exc;

             VI inters;
             VVI red; red.reserve(ZB.size());

             if (!excluded[v]) red.push_back(reducibles[v]);
             // red.push_back(reducibles[v]);
             for (int d : V[v]) if (!excluded[d]) red.push_back(reducibles[d]);
             // for (int d : V[v]) red.push_back(reducibles[d]);

             if (excluded[v] || red.size() >= 2)
             for ( auto & zb : red ) {
                 for (int d : zb) {
                     cnt[d]++;
                     if (cnt[d] == red.size()) inters.push_back(d);
                 }
             }
             for ( auto & zb : red ) for (int d : zb) cnt[d] = 0;

             if ( !inters.empty() ) {
                 clog << "Found recursively a set of reducible nodes: " << inters << endl;
                 changes = true;
                 fill(ALL(valid),false);

                 for (int d : inters) {
                     hit[d] = true;
                     for (int dd : V[d]) hit[dd] = true;
                     kernel.push_back(d);
                     in_kernel[d] = true;
                     to_lift.push_back( new ReducibleRule(d) );
                     GraphUtils::removeNodeFromGraph(V,d);
                 }

                 basic_rules();
                 // basic_rules_for_excluded();
                 // basic_rules();

                 // exit(1);
             }
         }

        if constexpr (make_measurements) timer.stop("recursive_reducer");

    };


    auto clique_N2 = [&]() {
        if constexpr (make_measurements) timer.start("clique_N2");

        auto inducesClique = [&](VI & zb)-> bool {
            if (zb.empty()) return true;
            for ( int d : zb ) if ( V[d].size()+1 < zb.size() ) return false;
            int cnt = 0;
            for ( int d : zb ) was[d] = true;
            for (int d : zb) {
                int c = 0;
                for ( int dd : V[d] ) c += was[dd];
                if ( c != zb.size()-1 ) break;
                cnt += c;
            }
            for ( int d : zb ) was[d] = false;
            return cnt == (zb.size() * (zb.size()-1));
        };

        constexpr int MAX_DEG = 6;
        VI N2;
        for ( int v=0; v<N; v++ ) if (!V[v].empty() && !hit[v] && V[v].size() <= MAX_DEG) {

            int unhit_dominator = -1;
            int unhit = 0;
            for (int d : V[v]) unhit += !hit[d];
            if (unhit <= 1) continue;

            {
                bool large_deg = false;
                for (int d : V[v]) large_deg |= ( V[d].size() > 2*MAX_DEG );
                if (large_deg) continue;
            }

            for (int d : V[v]) was[d] = true;
            for ( int w : V[v] ) {
                int c = !hit[w];
                for (int d : V[w]) c += (was[d] && !hit[d]);
                if ( c == unhit ) unhit_dominator = w;
            }
            for (int d : V[v]) was[d] = false;

            if ( unhit_dominator != -1 ) continue;

            N2.clear();
            for (int d : V[v]) was[d] = true; was[v] = true;
            for (int d : V[v]){
                for (int dd : V[d]) if (!was[dd]) {
                    was[dd] = true;
                    N2.push_back(dd);
                    if ( N2.size() > MAX_DEG ) break;
                }
                if ( N2.size() > MAX_DEG ) break;
            }
            for (int d : V[v]) was[d] = false; was[v] = false;
            for (int d : N2) was[d] = false;

            if ( N2.size() > MAX_DEG ) continue;

            if ( !N2.empty() && inducesClique(N2) ) {
                {
                    // clog << "Applied clique_N2 rule" << endl;
                    // DEBUG(v); DEBUG(N2); DEBUGV(V,v);
                    // for (int d : V[v]) DEBUGV(V,d);
                    // for (int d : N2) DEBUGV(V,d);
                    // exit(3);
                }
                hit[v] = true;
                for (int d : V[v]) hit[d] = true;
                kernel.push_back(v);
                in_kernel[v] = true;
                to_lift.push_back(new ReducibleRule(v));
                GraphUtils::removeNodeFromGraph(V, v);
                clique_N2_rules_applied++;
                changes = true;
            }
        }

        if constexpr (make_measurements) timer.stop("clique_N2");
    };


    auto applyFunnels = [&]() {
        if(true) if(!timer.tle(prepr_opt)) funnel3_nonfolding(); // here it seems to work alright
        // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(changes) basic_rules();
        if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(recent_funnel_rule_changes) basic_rules();
        // if(changes) continue;

        if(true) if(!timer.tle(prepr_opt)) funnel4_nonfolding();
        // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(changes) basic_rules();
        if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(recent_funnel_rule_changes) basic_rules();
        // if(changes) continue;

        if(true) if(!timer.tle(prepr_opt)) funnel5_nonfolding();
        // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(changes) basic_rules();
        if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(recent_funnel_rule_changes) basic_rules();
        // if(changes) continue;

        if(true) if(!timer.tle(prepr_opt)) funnel6_nonfolding();
        // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(changes) basic_rules();
        if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(recent_funnel_rule_changes) basic_rules();
        // if(changes) continue;

        if(true) if(!timer.tle(prepr_opt)) funnel7_nonfolding();
        // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(changes) basic_rules();
        if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(recent_funnel_rule_changes) basic_rules();
        // if(changes) continue;

        if(true) if(!timer.tle(prepr_opt)) funnel_folding(); // here it seems to work alright
        // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(changes) basic_rules();
        // if(changes) continue;
        return changes;
    };

    constexpr int XX_paths = 10;
    int preprocessing_path_rules_iterations = 0;

    constexpr int XX_basic_excluded = ( use_lossy_rules_for_excluded ? 10 : -1 );
    int preprocessing_basic_excluded_iterations = 0;

    constexpr int XX_funnels = inf; // funnel rules are used always in their first place
    int funnel_rules_iterations = 0;

    int preprocessing_iterations = 0;

    while(changes) {
        changes = false;
        preprocessing_iterations++;

        basic_rules();
        changes = false; // #TEST
        // if(changes) continue; // #TEST - with the improved basic rule it should not be necessary here,
        // as no edge will be removed or any node removed/marked further
        // so no need to double the computation
        if( timer.tle(prepr_opt) ) break;
        if(only_basic_reductions) break;


        if(true) if(!timer.tle(prepr_opt)) hit_N2();
        if(changes) continue;

        if(++preprocessing_path_rules_iterations <= XX_paths) {
            if(true) if(!timer.tle(prepr_opt)) path_rules(); // contraction
            if(changes) continue;

            if(true) if(!timer.tle(prepr_opt)) path_rules23(); // parallel paths rule
            if(changes) continue;
        }

        // if(true) if(!timer.tle(prepr_opt)) funnel3_nonfolding(); // here it seems to work alright
        // // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(changes) basic_rules();
        // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(recent_funnel_rule_changes) basic_rules();
        // // if(changes) continue;
        //
        // if(true) if(!timer.tle(prepr_opt)) funnel4_nonfolding();
        // // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(changes) basic_rules();
        // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(recent_funnel_rule_changes) basic_rules();
        // // if(changes) continue;
        //
        // if(true) if(!timer.tle(prepr_opt)) funnel5_nonfolding();
        // // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(changes) basic_rules();
        // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(recent_funnel_rule_changes) basic_rules();
        // // if(changes) continue;
        //
        // if(true) if(!timer.tle(prepr_opt)) funnel6_nonfolding();
        // // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(changes) basic_rules();
        // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(recent_funnel_rule_changes) basic_rules();
        // // if(changes) continue;
        //
        // if(true) if(!timer.tle(prepr_opt)) funnel7_nonfolding();
        // // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(changes) basic_rules();
        // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(recent_funnel_rule_changes) basic_rules();
        // // if(changes) continue;
        //
        // if(true) if(!timer.tle(prepr_opt)) funnel_folding(); // here it seems to work alright
        // // if constexpr (!remove_additional_nodes_in_funnels_on_the_spot) if(changes) basic_rules();
        // if(changes) continue;

        // if(true) if(!timer.tle(prepr_opt)) funnel2_nonfolding(); // this rules seems to be almost never used...
        // if(changes) continue;


        if (use_rules_for_excluded)
        if (++preprocessing_basic_excluded_iterations <= XX_basic_excluded) {
            // basic_rules_for_excluded(!use_lossy_rules_for_excluded);
            bool rem = basic_rules_for_excluded(false);
            if (rem) basic_rules();
            else changes = false;
        }

        if(++funnel_rules_iterations <= XX_funnels) {
            changes |= applyFunnels();
            if(changes) continue;
        }


        constexpr int variant = 1;
        if constexpr (variant == 0){
            if(true) if(!timer.tle(prepr_opt)) domination_rules2();
            if(changes) continue;

            if(true) if(!timer.tle(prepr_opt)) domination_rules();
            if(changes) continue;

            if(true) if(!timer.tle(prepr_opt)) domination_n123();
            if(changes) continue;

            if(true) if(!timer.tle(prepr_opt)) domination_rules3();
            if(changes) continue;

            if(true) if(!timer.tle(prepr_opt)) art_point_rules();
            if(changes) continue;
        }

        if constexpr (variant == 1){
            if(true) if(!timer.tle(prepr_opt)) domination_rules2();
            if(changes) continue;

            if(true) if(!timer.tle(prepr_opt)) art_point_rules();
            if(changes) continue;

            if(true) if(!timer.tle(prepr_opt)) domination_rules();
            if(changes) continue;

            if(true) if(!timer.tle(prepr_opt)) domination_rules3();
            if(changes) continue;

            if(true) if(!timer.tle(prepr_opt)) domination_n123();
            if(changes) continue;

            // if(true) if(!timer.tle(prepr_opt)) domination_rules4(); // this seems to give very little improvement...
            // if(changes) continue;
        }

        if(++funnel_rules_iterations > XX_funnels) {
            changes |= applyFunnels();
            if(changes) continue;
        }

        if (use_rules_for_excluded)
        if (preprocessing_basic_excluded_iterations > XX_basic_excluded)
        if ( ++preprocessing_basic_excluded_iterations <= 2*XX_basic_excluded) {
            // basic_rules_for_excluded(!use_lossy_rules_for_excluded);
            bool rem = basic_rules_for_excluded(false);
            if (rem) basic_rules();
            else changes = false;
        }

        if(true) if(!timer.tle(prepr_opt)) domination_n123_2nodes();
        if(changes) continue;

        if(true) if(!timer.tle(prepr_opt)) clique_N2(); // here it seems to work alright
        if(changes) continue;

        if(++preprocessing_path_rules_iterations > XX_paths) {
            if(true) if(!timer.tle(prepr_opt)) path_rules(); // contraction
            if(changes) continue;

            if(true) if(!timer.tle(prepr_opt)) path_rules23(); // parallel paths rule
            if(changes) continue;
        }

        if(false) // this does not offers any particular gains...
        if constexpr (use_lossy_rules_for_excluded) {
            if(true) if(!timer.tle(prepr_opt)) basic_rules_for_excluded(false);
            if (changes) continue;
        }

        if(true) if(!timer.tle(prepr_opt)) excluded_domination();
        if (changes) continue;


        if(true) if(!timer.tle(prepr_opt)) recursive_reductions(); // this is very time-consuming, by O(N) factor
        if (changes) continue;

    }


    if(!only_basic_reductions) if(timer.tle(prepr_opt)) {
        path_rules(); // contraction
        basic_rules();
    }

    if constexpr (use_rules_for_excluded) {
        if constexpr (use_lossy_rules_for_excluded) removeHitAndExcludedNodes();
        changes = true;
        while (changes) {
            changes = false;
            if constexpr (use_lossy_rules_for_excluded)
                if(!only_basic_reductions) basic_rules_for_excluded(false);

            if constexpr (!use_lossy_rules_for_excluded)
                if(!only_basic_reductions) basic_rules_for_excluded(true);

            basic_rules();
        } // this is just to mark some more excluded nodes using linear scan
    }
    if(!only_basic_reductions) small_connected_components();
    basic_rules();

    if constexpr (!use_rules_for_excluded) for ( int i=0; i<N; i++ ) assert( !excluded[i] ); // this is just for tests

    if constexpr (make_measurements) timer.stop("all_used_rules");

    // if constexpr( write_logs_and_stats ){
    if constexpr (enable_logs)
    if (recursive_reductions_level == 0) {
        DEBUG(preprocessing_iterations);
        DEBUG(kernel.size());
        DEBUG(excluded_and_hit_cnt);
        DEBUG(hit_edges_removed);
        DEBUG(excluded_edges_removed);
        DEBUG(hit_n2_cnt);
        DEBUG(clique_N2_rules_applied);
        DEBUG(domination_rules_applied);
        DEBUG(domination_rules2_applied);
        DEBUG(domination_rules3_applied);
        DEBUG(domination_rules4_applied);
        DEBUG(domination_n123_rules_applied);
        DEBUG(domination_n123_2nodes_rules_applied);
        DEBUG(bipartite_domination_rules_applied);
        DEBUG(path_rules_applied);
        DEBUG(path_rules2_applied);
        DEBUG(path_rules3_applied);
        DEBUG(path_rules3_applied_value_2);
        DEBUG(path_rules3_applied_value_3);
        DEBUG(path_rules3_applied_value_4);
        DEBUG(path_rules3_applied_value_5);
        DEBUG(art_point_rules_applied);
        DEBUG(small_conn_comp_considered);
        DEBUG(funnel_folding_rules_applied);
        // DEBUG(funnel_domination_rules_applied);
        DEBUG(funnel2_nonfolding_applied);
        DEBUG(funnel3_nonfolding_rules_applied);
        DEBUG(funnel4_nonfolding_applied);
        DEBUG(funnel5_nonfolding_applied);
        DEBUG(funnel6_nonfolding_applied);
        DEBUG(funnel7_nonfolding_applied);
        DEBUG(excluded_domination_applied);
        DEBUG(recursive_reducer_applied);
        DEBUG(basic_excluded_marked);
        DEBUG(to_lift.size());
        DEBUG(accumulate(ALL(hit),0));

        if constexpr (enable_logs)
        if constexpr (make_measurements) timer.writeAll();
    }
    // }

    constexpr bool write_final_path_sizes = true;
    if constexpr (write_final_path_sizes ) if (recursive_reductions_level == 0) {
        map<int,int> paths_with_internal_nodes_cnt_non_cycle;

        for( int v=0; v<N; v++ ) {
            if( V[v].size() <= 2 ) continue;

            for( int d : V[v] ) if ( V[d].size() == 2 ) {
                int u = d, prev = v;
                int path_size = 1;
                while( V[u].size() == 2 && u != v ) {
                    path_size++;
                    if( V[u][0] == prev ) { prev = u; u = V[u][1]; }
                    else { prev = u; u = V[u][0]; }
                }
                path_size++;
                int internal_nodes = path_size-2;
                if (u < v) paths_with_internal_nodes_cnt_non_cycle[internal_nodes]++;
            }
        }
        if constexpr (enable_logs) DEBUG(paths_with_internal_nodes_cnt_non_cycle);
    }

    timer.stop(prepr_opt);

    for (int i=0; i<N; i++) checkAndUnmarkExcludedNode(i);

    return {kernel,hit,excluded,permanent_excluded_node_unhit_dominator,to_lift};
}
