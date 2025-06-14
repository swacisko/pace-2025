//
// Created by sylwe on 04/05/2025.
//

#include "DSSE.h"

#include <CombinatoricUtils.h>

#include "DominatingSetSolver.h"
#include "GraphInducer.h"
#include "components/ConnectedComponents.h"
#include "CollectionOperators.h"
#include "GraphUtils.h"
#include <filesystem>
#include "Pace25Utils.h"
#include "HittingSetLS.h"

VI DSSE::solve(bool add_isolated_nodes, bool use_reductions, bool consider_connected_components) {
    VI res;
    int N = V.size();
    if (add_isolated_nodes) for (int i=0; i<N; i++) if (V[i].empty()) res.push_back(i);

    VVI comps;
    if (consider_connected_components) comps = ConnectedComponents::getConnectedComponents(V);
    else {
        comps = {VI(N)};
        iota(ALL(comps[0]),0);
    }

    for ( auto & cmp : comps ) if ( cmp.size() >= 2 ) {
        auto g = GraphInducer::induce(V, cmp);
        int n = g.V.size();
        VB ind_hit(n), ind_exc(n), ind_forb(n);
        for ( int i=0; i<n; i++ ) ind_hit[i] = hit_nodes[g.nodes[i]];
        for ( int i=0; i<n; i++ ) ind_exc[i] = excluded_nodes[g.nodes[i]];
        for ( int i=0; i<n; i++ ) ind_forb[i] = forbidden_nodes[g.nodes[i]];

        DSSE dsse( g.V, ind_hit, ind_exc, ind_forb, 0 );
        dsse.exact_hs_solving_method = exact_hs_solving_method;
        VI res_g = dsse.solveForConnected(use_reductions);
        g.remapNodes(res_g);
        res += res_g;
    }

    // assert( DominatingSetSolver::isCorrect(V,res,1,hit_nodes) );
    return res;
}


VI DSSE::solveForConnected(bool use_reductions) {

    constexpr bool write_logs = false;

    int N = V.size();
    int M = GraphUtils::countEdges(V);

    if constexpr (write_logs) {
        indent(); clog << "Entering solveForConnected, (N,M) : (" << N << "," << M << ")" << endl;
    }

    VI all_nodes(N);
    iota(ALL(all_nodes),0);

    auto V0 = V;
    auto hit_nodes_0 = hit_nodes;
    auto excluded_nodes_0 = excluded_nodes;
    auto forbidden_nodes_0 = forbidden_nodes;
    auto revertToOriginalState = [&]() {
        V = V0;
        hit_nodes = hit_nodes_0;
        excluded_nodes = excluded_nodes_0;
        forbidden_nodes = forbidden_nodes_0;
    };

    vector<LiftableRule*> to_lift;
    if (use_reductions) {
        int status;
        tie(status,to_lift) = preprocessForExact();
        if ( status != 0 ) {
            for (auto * r : to_lift) delete r;
            return all_nodes;
        }
    }

    VI res;


    auto liftRes = [&](VI & res, bool delete_rules = true) {
        VB res_mask = StandardUtils::toVB( N, res);
        reverse(ALL(to_lift));
        for( auto * dr : to_lift ) dr->lift(res_mask);
        if(delete_rules) {
            for( auto * dr : to_lift ) delete dr;
            to_lift.clear();
        }
        res = StandardUtils::toVI(res_mask);
    };


    { // checks if the graph is empty after reductions - if so, then we can lift solution and return it
        bool is_empty = true;
        for ( auto & v : V ) is_empty &= v.empty();
        if (is_empty) {
            if constexpr (write_logs) {
                indent(); clog << "after preprocessing graph is empty, lifting and returning solution" << endl;
            }
            revertToOriginalState();
            liftRes(res, false);
            assert(assertCorrectnessAndWrite(V,res,
                hit_nodes, excluded_nodes, forbidden_nodes, to_lift));

            for( auto * r : to_lift ) delete r;
            assert(isCorrect(V,res,hit_nodes));
            assert( DominatingSetSolver::isCorrect(V,res,1,hit_nodes) );
            return res;
        }
    }



    if( (rec_depth >= rec_depth_for_hs_solver) && ( exact_hs_solving_method != NONE ) ){ // solve HS instance
        if constexpr(write_logs) {
            indent();
            clog << "Solving (sub)problem HS instance using " << ( (exact_hs_solving_method == MILP) ? "milp" : "findminhs" )
                 << ", N: " << V.size() << ", M: " << GraphUtils::countEdges(V) << endl;
        }

        VI RR;
        if(true){
            RR = findOptimalResultsHS();
            if constexpr(write_logs) {indent(); DEBUG(RR.size());}
            assert(assertCorrectnessAndWrite(V,RR,
                hit_nodes, excluded_nodes, forbidden_nodes, {}));
        }

        if(false){
            auto comps = ConnectedComponents::getConnectedComponents(V);
            for ( auto & cmp : comps ) if (cmp.size() >= 2) {
                auto g = GraphInducer::induce(V, cmp);
                int n = g.V.size();
                VB ind_hit(n), ind_exc(n), ind_forb(n);
                for ( int i=0; i<n; i++ ) ind_hit[i] = hit_nodes[g.nodes[i]];
                for ( int i=0; i<n; i++ ) ind_exc[i] = excluded_nodes[g.nodes[i]];
                for ( int i=0; i<n; i++ ) ind_forb[i] = forbidden_nodes[g.nodes[i]];

                DSSE dsse( g.V, ind_hit, ind_exc, ind_forb, rec_depth+1 );
                dsse.exact_hs_solving_method = exact_hs_solving_method;
                VI res_g = dsse.findOptimalResultsHS();
                assert( DominatingSetSolver::isCorrect(g.V, res_g, 1,ind_hit) );
                g.remapNodes(res_g);
                RR+= res_g;
            }
        }

        liftRes(RR);
        revertToOriginalState();
        assert(isCorrect(V,RR,hit_nodes));
        assert( DominatingSetSolver::isCorrect(V,RR,1,hit_nodes) );
        return RR;
    }


    VI res1, res2;

    int branch_node = getNodeToBranch();

    if (branch_node == -1) { // all nodes are forbidden...
        assert(false);
        if constexpr (write_logs) {
            indent(); clog << "no valid branching node, returning solution of size N: " << N << endl;
        }
        revertToOriginalState();
        for (auto * r : to_lift) delete r;
        return all_nodes;
    }

    assert(!forbidden_nodes[branch_node]);

    if constexpr (write_logs) {
        indent();
        clog << "branching on node branch_node: " << branch_node
            << ", deg: " << V[branch_node].size() << ", hit: " << hit_nodes[branch_node] << endl;
    }

    { // branch1 - adding branch_node to solution
        if constexpr (write_logs) {
            indent(); clog << "branch 1 - adding node" << endl;
        }

        DSSE self_cp = *this;

        res1.push_back(branch_node);
        hit_nodes[branch_node] = true;
        for ( int d : V[branch_node] ) hit_nodes[d] = true;
        GraphUtils::removeNodeFromGraph(V,branch_node);

        auto comps = ConnectedComponents::getConnectedComponents(V);
        for ( auto & cmp : comps ) if (cmp.size() >= 2) {
            auto g = GraphInducer::induce(V, cmp);
            int n = g.V.size();
            VB ind_hit(n), ind_exc(n), ind_forb(n);
            for ( int i=0; i<n; i++ ) ind_hit[i] = hit_nodes[g.nodes[i]];
            for ( int i=0; i<n; i++ ) ind_exc[i] = excluded_nodes[g.nodes[i]];
            for ( int i=0; i<n; i++ ) ind_forb[i] = forbidden_nodes[g.nodes[i]];

            DSSE dsse( g.V, ind_hit, ind_exc, ind_forb, rec_depth+1 );
            dsse.exact_hs_solving_method = exact_hs_solving_method;
            VI res_g = dsse.solveForConnected(true);
            assert( DominatingSetSolver::isCorrect(g.V, res_g, 1,ind_hit) );
            g.remapNodes(res_g);
            res1+= res_g;
        }

        assert( isCorrect(V,res1,hit_nodes) );

        V = self_cp.V;
        hit_nodes = self_cp.hit_nodes;
        excluded_nodes = self_cp.excluded_nodes;
        forbidden_nodes = self_cp.forbidden_nodes;

        assert(assertCorrectnessAndWrite(V,res1,
                hit_nodes, excluded_nodes, forbidden_nodes, {}));

        if constexpr (write_logs) {
            indent(); DEBUG(res1.size());
        }
    }

    { // branch2 - forbidding to branch_node to solution
        if constexpr (write_logs) {
            indent(); clog << "branch 2 - forbidding node" << endl;
        }

        DSSE self_cp = *this;

        bool can_be_valid = true;
        forbidden_nodes[branch_node] = true;
        if ( hit_nodes[branch_node] ) {
            // we need to add all adjacent leaves to the solution before removing branch_node from the graph...
            for( int d : V[branch_node] ) if( V[d].size() == 1 && !hit_nodes[d] ) {
                res2.push_back(d);
                hit_nodes[d] = hit_nodes[branch_node] = true;
                if( forbidden_nodes[d] ) can_be_valid = false; // if d is forbidden...
            }
            GraphUtils::removeNodeFromGraph(V,branch_node);
        }

        if(can_be_valid) {
            auto comps = ConnectedComponents::getConnectedComponents(V);
            for ( auto & cmp : comps ) if (cmp.size() >= 2) {
                auto g = GraphInducer::induce(V, cmp);
                int n = g.V.size();
                VB ind_hit(n), ind_exc(n), ind_forb(n);
                for ( int i=0; i<n; i++ ) ind_hit[i] = hit_nodes[g.nodes[i]];
                for ( int i=0; i<n; i++ ) ind_exc[i] = excluded_nodes[g.nodes[i]];
                for ( int i=0; i<n; i++ ) ind_forb[i] = forbidden_nodes[g.nodes[i]];

                DSSE dsse( g.V, ind_hit, ind_exc, ind_forb, rec_depth+1 );
                dsse.exact_hs_solving_method = exact_hs_solving_method;
                VI res_g = dsse.solveForConnected(true);
                g.remapNodes(res_g);
                res2+= res_g;
            }
        }else {
            res2 = all_nodes;
        }

        assert( isCorrect(V,res2,hit_nodes) );

        V = self_cp.V;
        hit_nodes = self_cp.hit_nodes;
        excluded_nodes = self_cp.excluded_nodes;
        forbidden_nodes = self_cp.forbidden_nodes;

        assert(assertCorrectnessAndWrite(V,res2,
               hit_nodes, excluded_nodes, forbidden_nodes, {}));

        if constexpr (write_logs) {
            indent(); DEBUG(res2.size());
        }
    }

    if ( res1.size() < res2.size() ) res += res1;
    else res += res2;

    revertToOriginalState();
    if (use_reductions) liftRes(res,false);

    assert(assertCorrectnessAndWrite(V,res,
               hit_nodes, excluded_nodes, forbidden_nodes, to_lift));
    assert( DominatingSetSolver::isCorrect(V,res,1,hit_nodes) ); // this must hold, as V was connected
    for(auto * r : to_lift) delete r;

    if constexpr (write_logs) {
        indent(); clog << "Found recursively result for graph (N,M) : (" << N << "," << M << "), res.size(): " << res.size() << endl;
    }

    return res;

}

bool DSSE::isCorrect(VVI &V, VI & res, VB &hit, bool disregard_isolated_nodes) {
    int N = V.size();
    VB was = StandardUtils::toVB(N,res);
    for(int i=0; i<N; i++) if( !was[i] && !hit[i] ) {
        if(disregard_isolated_nodes && V[i].empty()) continue;
        bool h = false;
        for( int d : V[i] ) h |= was[d];
        if( !h ) return false;
    }
    return true;
}

void DSSE::writeUnhitNodes(VVI& V, VI& res, VB& hit, bool disregard_isolated_nodes) {
    int N = V.size();
    VB was = StandardUtils::toVB(N,res);
    for(int i=0; i<N; i++) if( !was[i] && !hit[i] ) {
        if(disregard_isolated_nodes && V[i].empty()) continue;
        bool h = false;
        for( int d : V[i] ) h |= was[d];
        if( !h ) {
            clog << "node " << i << " is unhit, "; DEBUGV(V,i);
        }
    }
}

void DSSE::writeRules(vector<LiftableRule*> lft) {
    clog << "Applied reduction rules: " << endl;
    for(auto * r : lft) {
        DEBUG(r->getName());
        DEBUG(r->getDescription());
        ENDL(1);
    }
}

bool DSSE::assertCorrectnessAndWrite(VVI& V, VI& res, VB& hit, VB& exc, VB& forb, vector<LiftableRule*> lft,
    bool disregard_isolated_nodes) {
    if( !isCorrect(V,res,hit,disregard_isolated_nodes) ) {
        indent(); clog << "Assertion fail" << endl;
        DEBUG(res);
        writeUnhitNodes(V,res,hit);
        writeRules(lft);
        GraphUtils::writeGraphHumanReadable(V);
        DEBUG(hit); DEBUG(exc); DEBUG(forb);
        return false;
    }
    return true;
}

VI DSSE::createReducibleNodes(vector<LiftableRule*>& lft) {
    VI reducibles;
    for ( auto * r : lft ) {
        if ( r->getName() == "reducible" ) {
            auto rr = dynamic_cast<ReducibleRule*>(r);
            reducibles.push_back(rr->v);
        }
    }
    return reducibles;
}

int DSSE::getNodeToBranch() {
    int N = V.size();
    int res_v = -1;
    int res_val_forb = 0; // the larger, the better
    int res_val_unhit = inf; // the smaller, the better

    for ( int v =0; v<N; v++ ) if ( !forbidden_nodes[v] ) {
    // for ( int v =0; v<N; v++ ) if ( !excluded_nodes[v] && !forbidden_nodes[v] ) {
        int c = 0;
        for ( int d : V[v] ) c += forbidden_nodes[d];
        if ( c > res_val_forb ) {
            res_val_forb = c;
            res_v = v;
        }
        else if ( c < res_val_forb ) continue;

        c = 0;
        for ( int d : V[v] ) c += !hit_nodes[d];
        if ( c < res_val_unhit ) {
            res_val_unhit = c;
            res_v = v;
        }
        else if ( c > res_val_unhit ) continue;
    }

    // indent();
    // clog << "found branching node res_v: " << res_v << " with: forbidden neighbors: " << res_val_forb
    //      << ", unhit_neighbors: " << res_val_unhit << endl;


    return res_v;
}


int DSSE::getNodeToBranchOld() {
    // int v = -1;
    // int d = -1;
    int N = V.size();

    VI covers_unhit(N,0);
    VI hits_forbidden(N,0);
    VI hits_unexcluded(N,0);
    VI hits_excluded(N,0);
    VI N2_factor(N,0);
    VB was(N);

    for( int i=0; i<N; i++ ) {
        covers_unhit[i] = !hit_nodes[i];
        for( int d : V[i] ) covers_unhit[i] += !hit_nodes[d];

        hits_forbidden[i] += forbidden_nodes[i];
        for( int d : V[i] ) covers_unhit[i] += forbidden_nodes[d];

        hits_unexcluded[i] += !excluded_nodes[i];
        for( int d : V[i] ) hits_unexcluded[i] += !excluded_nodes[d];

        hits_excluded[i] = V[i].size() - hits_unexcluded[i];

        VI temp;
        for( int d : V[i] ) was[d] = true;
        for( int d : V[i] ) for( int dd : V[d] ) if( !was[dd] ) {
            was[dd] = true;
            N2_factor[i] += 1 + !hit_nodes[dd] + !excluded_nodes[dd] + forbidden_nodes[dd];
            temp.push_back(dd);
        }
        for( int d : V[i] ) was[d] = false;
        for( int d : temp ) was[d] = false;
    }

    constexpr int invalid_branch = 1e9;

    auto assessEffectOfBranchingOnNode = [&](int branch_node) {
        int R1, R2 = 0;

        constexpr int opt = 2;

        bool can_be_valid = true;

         { // branch1 - adding branch_node to solution

            DSSE self_cp = *this;

            hit_nodes[branch_node] = true;
            for ( int d : V[branch_node] ) hit_nodes[d] = true;
            GraphUtils::removeNodeFromGraph(V,branch_node);

            DSReducer red(hit_nodes, excluded_nodes);
            red.recursive_reductions_level = 1;
            auto [kernel,hit,exc,penud,lft] =
                red.reductionRulesDS(V,inf,false);
            lft.push_back( new ReducibleRule(branch_node) );


            if constexpr (opt == 1) R1 = lft.size(); // option1: number of rules to lift
            if constexpr (opt == 2) for( int i=0; i<N; i++ ) R1 += V[i].size(); // option2: graph size after reduction
            if constexpr (opt == 3) for( int i=0; i<N; i++ ) R1 += !V[i].empty(); // option3: number of nonisolated nodes

            for(auto * r : lft) delete r;
            // V = self_cp.V;
            swap(V,self_cp.V);
            hit_nodes = self_cp.hit_nodes;
            excluded_nodes = self_cp.excluded_nodes;
            forbidden_nodes = self_cp.forbidden_nodes;
        }

        { // branch2 - forbidding to branch_node to solution

            DSSE self_cp = *this;

            int added = -1;
            forbidden_nodes[branch_node] = true;
            if ( hit_nodes[branch_node] ) {
                for( int d : V[branch_node] ) if( V[d].size() == 1 && !hit_nodes[d] ) {
                    added = d;
                    hit_nodes[d] = hit_nodes[branch_node] = true;
                    if( forbidden_nodes[d] ) can_be_valid = false; // if d is forbidden...
                }
                GraphUtils::removeNodeFromGraph(V,branch_node);
            }

            DSReducer red(hit_nodes, excluded_nodes);
            red.recursive_reductions_level = 1;
            auto [kernel,hit,exc,penud,lft] =
                red.reductionRulesDS(V,inf,false);
            if(added != -1) lft.push_back(new ReducibleRule(added));

            if constexpr (opt == 1) R2 = lft.size(); // option1: number of rules to lift
            if constexpr (opt == 2) for( int i=0; i<N; i++ ) R2 += V[i].size(); // option2: graph size after reduction
            if constexpr (opt == 3) for( int i=0; i<N; i++ ) R2 += !V[i].empty(); // option3: number of nonisolated nodes

            for(auto * r : lft) delete r;
            // V = self_cp.V;
            swap(V, self_cp.V);
            hit_nodes = self_cp.hit_nodes;
            excluded_nodes = self_cp.excluded_nodes;
            forbidden_nodes = self_cp.forbidden_nodes;
        }

        if(!can_be_valid) return invalid_branch; // if one branch cannot be valid, take the branching node
        // if(!can_be_valid) R2 = invalid_branch;

        if constexpr (opt == 1) { // the larger the value, the better
            return min(R1,R2);
            // return R1+R2;
        }
        if constexpr (opt == 2) { // the larger the value, the better
            return -max(R1,R2); // this seems to work best among all options...
            // return -R1-R2;
        }
        if constexpr (opt == 3) { // the larger the value, the better
            return -max(R1,R2);
            // return -R1-R2;
        }
    };

    auto cmp = [&](int a, int b) {
        return
            // 2*covers_unhit[a] + N2_factor[a]
            // 2*covers_unhit[a] + hits_forbidden[a] + hits_unexcluded[a] + V[a].size() + N2_factor[a]
            covers_unhit[a] + hits_forbidden[a] + hits_unexcluded[a] + V[a].size() // original
            // 2*covers_unhit[a] + hits_forbidden[a] + hits_unexcluded[a] - V[a].size()
            // 2*covers_unhit[a] + hits_forbidden[a] + hits_excluded[a]
            >
            // 2*covers_unhit[b] + N2_factor[b];
            // 2*covers_unhit[b] + hits_forbidden[b] + hits_unexcluded[b] + V[b].size() + N2_factor[b];
            covers_unhit[b] + hits_forbidden[b] + hits_unexcluded[b] + V[b].size(); // original
        // 2*covers_unhit[b] + hits_forbidden[b] + hits_unexcluded[b] - V[b].size();
        // 2*covers_unhit[b] + hits_forbidden[b] + hits_excluded[b];
    };

    VI perm = CombinatoricUtils::getRandomPermutation(N);
    sort(ALL(perm), cmp );
    // sort(ALL(perm), [&](int a, int b){ return 2*covers_unhit[a] + V[a].size() > 2*covers_unhit[b] + V[b].size(); });
    // sort(ALL(perm), [&](int a, int b){ return V[a].size() - covers_unhit[a]  > V[b].size() - covers_unhit[b]; });
    // sort(ALL(perm), [&](int a, int b){ return V[a].size() > V[b].size(); });
    // sort(ALL(perm), [&](int a, int b){ return hits_forbidden[a] > hits_forbidden[b]; });
    // sort(ALL(perm), [&](int a, int b){ return covers_unhit[a] > covers_unhit[b]; });

    int selection_type = 0; // version 1 is much better for 'larger instances', but version 0 is faster for very small
    int v = -1;

    if (selection_type == 1) {
        v = -1;
        int m = -inf;
        // for ( int i : perm) if (!forbidden_nodes[i] && !V[i].empty()) {
        // for ( int i : perm) if (!forbidden_nodes[i] && !V[i].empty() && !excluded_nodes[i]) {
        // for ( int i : perm) if (!forbidden_nodes[i] && !V[i].empty() && hit_nodes[i]) {
        for ( int i : perm) if (!forbidden_nodes[i] && !V[i].empty() && hit_nodes[i] && !excluded_nodes[i]) {
            int r = assessEffectOfBranchingOnNode(i);
            if( m < r ) { // select the largest effect of branching on node i
                m = r;
                v = i;
            }
        }
        if( v == -1 ) selection_type = 0;
    }

    if (selection_type == 0) {
        // int forb_neigh_v = 0;

        for ( int i : perm) if (!forbidden_nodes[i] && !V[i].empty()) { // original
            if ( v == -1 ) v = i;
            if ( (!hit_nodes[v] && hit_nodes[i]) ) v = i;
            if ( hit_nodes[v] != hit_nodes[i] ) continue;
            if ( (excluded_nodes[v] && !excluded_nodes[i]) ) v = i;

            // int forb_neigh = 0;
            // for( int d : V[i] ) forb_neigh += forbidden_nodes[d];
            //
            // if( forb_neigh > forb_neigh_v ){ v = i; forb_neigh_v = forb_neigh; }

            // if( hits_uncovered[i] > hits_uncovered[v] ) v = i;
            // else if(hits_uncovered[i] == hits_uncovered[v]) {
            //     // if ( hits_forbidden[i] > hits_forbidden[v] ) v = i; // #TEST
            //     // else if( hits_forbidden[i] == hits_forbidden[v] ) {
            //
            //         // if ( excluded_nodes[v] && !excluded_nodes[i] ) v = i;
            //         // else if( !excluded_nodes[i] ) {
            //             if(V[i].size() > V[v].size()) v = i;
            //         // }
            //
            //     // }
            // }

            // if(cmp(i,v)) v = i;

            // if ( V[i].size() > V[V].size() ) v = i; // select node with largest degree
            // if ( V[i].size() < V[v].size() ) v = i; // select node with smallest degree

        }
    }


    return v; // it might return -1, meaning that we cannot branch, as all nodes are forbidden...
}


VI DSSE::findOptimalResultsHS() {
    VVI sets;
    int N = V.size();
    VI dst(N,inf);
    VB was(N);
    for( int v=0; v<N; v++ ) if (!V[v].empty() && !hit_nodes[v]) {
        auto reachables = findReachableNodesFromSWithinDistanceK(V,{v},1,dst,was);
        sets.push_back(reachables);
    }

    constexpr bool remove_excluded = true;
    if constexpr (remove_excluded) {
        // #TEST #CAUTION can we remove excluded and forbidden nodes from the sets??
        for( auto & v : sets ) REMCVAL( excluded_nodes, v );
        for( auto & v : sets ) REMCVAL( forbidden_nodes, v );
        for(int i=(int)sets.size()-1; i>=0; i--) if( sets[i].empty() ) REM(sets,i);
    }

    VI mapper(N,-1), remapper(N,-1);
    {
        set<int> zb;
        for(auto & v : sets) zb.insert(ALL(v));
        int cnt = 0;
        for(int d : zb) {
            mapper[d] = cnt;
            remapper[cnt] = d;
            cnt++;
        }

        for( auto & v : sets ) for(int & d : v) d = mapper[d];
    }

    set<int> zb;
    for (auto & s : sets) zb.insert(ALL(s));
    int different_elements = zb.size();

    indent(); clog << "There are " << sets.size() << " sets to hit, different_elements: "
            << different_elements << endl;


    auto r = findMHSForSets(sets, exact_hs_solving_method);
    for(int & d : r) d = remapper[d];
    return r;
}


VI DSSE::solveIterative() {
    Stopwatch timer;
    DSS dss(timer);
    dss.find_exact_result = true;
    dss.exact_hs_solving_method = exact_hs_solving_method;
    auto res = dss.solveH(V,1,true,inf);
    return res;
}

VI DSSE::findMHSForSets(VVI &sets, HSMethod hs_solving_method, int time_limit_millis, VI upper_bound_solution, int lower_bound) {
    if(hs_solving_method == MILP) {
        // IntGenerator rnd;
        UniformIntGenerator rnd(0,LLONG_MAX>>2);
        auto r = rnd.rand();
        string filename = "temp_hsg" + to_string(r) + ".txt";

        ofstream str(filename);

        VVI A = HittingSetLS::createV(sets);
        VVI B = sets;
        int N = A.size(), M = B.size();

        str << N << " " << M << endl;
        for (int i = 0; i < N; i++) {
            str << A[i].size() << "\n";
            for (int d: A[i]) str << d << " ";
            if (!A[i].empty()) str << "\n";
        }

        for (int i = 0; i < N; i++) str << 1 << " ";
        str << endl;
        str.close();

        string res_filename = filename + ".res";
        string command = "python3 solveILP.py < " + filename + " > " + res_filename;

        auto a = system(command.c_str());

        VI res;
        {
            double milp_time_millis = 0;
            ifstream str( res_filename );
            str >> milp_time_millis;
            int len;
            str >> len;
            if( len > 0 ){
                assert(len == A.size());
                for( int i=0; i<A.size(); i++ ){
                    int val;
                    str >> val;
                    if(val) res.push_back(i);
                }
            }
        }

        // removing temporary files
        filesystem::remove(filename);
        filesystem::remove(res_filename);

        int value = accumulate( ALL(res), 0, [&](auto res, auto r){ return res + 1; } );
        if( res.empty() ) value = -1;

        return res;
    }

    if(hs_solving_method == FINDMINHS) {
        return findMHSForSetsFINDMINHS(sets, upper_bound_solution, lower_bound);
    }

    if(hs_solving_method == SAT) {
        return findMHSForSetsSAT(sets);
    }

    if(hs_solving_method == CPSAT) {
        return findMHSForSetsCPSAT(sets, time_limit_millis);
    }

    if(hs_solving_method == ILPOR) {
        return findMHSForSetsILPOR(sets);
    }

    assert( false && "invalid HS solving method selected" );
    return {};
}

// tuple<VB,VB,vector<LiftableRule*>> DSSE::preprocessForExact() {
pair<int,vector<LiftableRule*>> DSSE::preprocessForExact() {
    vector<LiftableRule*> to_lift;

    int N = V.size();
    int status = 0; // 0 - ok, 1 = no valid solution, no need to consider further

    bool changes = true;
    while (changes) {

        // for( int i=0; i<N; i++ ) if(forbidden_nodes[i]) excluded_nodes[i] = true; // #TEST - is this correct?
        // for( int i=0; i<N; i++ ) if(excluded_nodes[i]) forbidden_nodes[i] = true; // #TEST - this is incorrect...

        Stopwatch temp_sw;
        DSReducer dss(hit_nodes, excluded_nodes);
        dss.recursive_reductions_level = 1; // this muffles the reducer and hides all logs
        // dss.use_recursive_reducer = (rec_depth == 0);
        auto [kern, hit, exc, penud,lft] = dss.reductionRulesDS(V,reductions_time_liimt,false);
        to_lift += lft;
        hit_nodes = hit;
        excluded_nodes = exc;

        changes = false;


        constexpr bool remove_edges_between_forbidden_nodes = true;
        auto forbiddenEdgeRemoval = [&]() {
            if constexpr (remove_edges_between_forbidden_nodes) {
                // edge between two forbidden nodes can be removed
                for ( int i=0; i<N; i++ ) if (!V[i].empty() && forbidden_nodes[i]) {
                    int s = V[i].size();
                    REMCVAL( forbidden_nodes, V[i] );
                    if ( V[i].size() < s ) changes = true;
                    if ( V[i].empty() && !hit_nodes[i] ) {
                        assert( false && "forbidden isolated node is not hit" );
                        status = 1;
                        return;
                    }
                }
            }
        };


        forbiddenEdgeRemoval();
        if (status) break;

        {
            VI reducibles = createReducibleNodes(to_lift);
            bool red_forb = false;
            for (int d : reducibles) red_forb |= forbidden_nodes[d];
            if (red_forb) {
                status = 1;
                break;
            }
        }


        // now using forbidden rules
        constexpr bool remove_hit_and_forbidden_nodes = true;
        if constexpr(remove_hit_and_forbidden_nodes) { // we can safely delete all nodes that are hit and forbidden
            for ( int i=0; i<N; i++ ) if ( forbidden_nodes[i] && hit_nodes[i] && !V[i].empty() ) {
                for(int a : V[i]) if ( V[a].size() == 1 && !hit_nodes[a] ) {
                    to_lift.push_back( new ReducibleRule(a) );
                    hit_nodes[a] = true;
                }
                GraphUtils::removeNodeFromGraph(V,i);
                changes = true;
            }
        }

        forbiddenEdgeRemoval();
        if (status) break;


        constexpr bool surrounded_by_forbidden = true;
        if constexpr (surrounded_by_forbidden) {
            // if a node v is unhit and all its neighbors are forbidden, then we can add v to the solution

            for ( int i=0; i<N; i++ ) if (!V[i].empty() && !hit_nodes[i]) {
                int cnt = 0, neigh = -1;
                for (int d : V[i]) {
                    cnt += forbidden_nodes[d];
                    if (!forbidden_nodes[d]) neigh = d;
                }
                if (cnt == V[i].size()) {
                    hit_nodes[i] = true;
                    for (int d : V[i]) hit_nodes[d] = true;
                    to_lift.push_back( new ReducibleRule(i) );
                    GraphUtils::removeNodeFromGraph(V,i);
                    changes = true;
                }
                if ( forbidden_nodes[i] && cnt+1 == V[i].size() ) {
                    hit_nodes[neigh] = true;
                    for (int d : V[neigh]) hit_nodes[d] = true;
                    to_lift.push_back( new ReducibleRule(neigh) );
                    GraphUtils::removeNodeFromGraph(V,neigh);
                    changes = true;
                }
            }
        }

        forbiddenEdgeRemoval();
        if (status) break;

    }

    if (status) {
        for ( auto * r : to_lift ) delete r;
        to_lift.clear();
    }


    // return {res_hit, res_exc, to_lift};
    return {status,to_lift};
}

VI DSSE::findMHSForSetsFINDMINHS(VVI &sets, VI upper_bound_solution, int lower_bound) {
    assert(filesystem::exists("findminhs"));

    // IntGenerator rnd;
    UniformIntGenerator rnd(0,LLONG_MAX>>2);
    int r = rnd.rand();

    string infile = "hs_in.txt" + to_string(r);
    ofstream str(infile.c_str());
    int N = 0;
    for( VI & C : sets ) for( int d : C ) N = max(d,N);
    str << N+1 << " " << sets.size() << endl;
    for( VI & C : sets ){
        str << C.size();
        for( int d : C ) str << " " << d;
        str << endl;
    }
    str.close();


    string settings_file = "hs_settings.txt" + to_string(r);
    str.open( settings_file.c_str() );
    ostringstream sett_str;

    sett_str << "{\n" <<
                      "    \"enable_local_search\": true,\n" << // original
//                          "    \"enable_local_search\": false,\n" << // #TEST
                      "    \"enable_max_degree_bound\": true,\n" <<
                      "    \"enable_sum_degree_bound\": false,\n" <<
                      "    \"enable_efficiency_bound\": true,\n" <<
                      "    \"enable_packing_bound\": true,\n" <<
                      "    \"enable_sum_over_packing_bound\": true,\n" <<
//                          "    \"packing_from_scratch_limit\": 5,\n" << // original
                      "    \"packing_from_scratch_limit\": 3,\n" << // #TEST
//                          "    \"greedy_mode\": \"AlwaysBeforeBounds\"\n" <<
//                          "    \"greedy_mode\": \"AlwaysBeforeExpensiveReductions\""; // original
                      "    \"greedy_mode\": \"Once\""; // #TEST
    if(!upper_bound_solution.empty()){
        sett_str << ",\n    \"initial_hitting_set\": [";
        int cnt = 0;
        for(int d : upper_bound_solution){
            if(cnt++ > 0) sett_str << ",";
            sett_str << d;
        }
        sett_str << "]";
    }

    if(lower_bound > 0){
        sett_str << ",\n    \"stop_at\": " << lower_bound;
    }

    sett_str << "\n}";
    string settings = sett_str.str();

    str << settings << endl;
    str.close();

    string report_file = "hs_report.txt" + to_string(r);
    string out_file = "hs_out.txt" + to_string(r);
    string log_file = "hs_log.txt" + to_string(r);
//        string command = "./findminhs solve " + infile + " " + settings_file + " -r " + report_file;
    string command = "./findminhs solve " + infile + " " + settings_file + " > " + out_file;
//        string command = "./findminhs solve " + infile + " " + settings_file + " > " + out_file + " 2> " + log_file;
    auto suppress = system(command.c_str());


    ifstream istr(out_file.c_str());
    string s;
    vector<string> lines;
    while( istr >> s ) lines.push_back(s);
    istr.close();

    filesystem::remove(infile);
    filesystem::remove(settings_file);
    filesystem::remove(report_file);
    filesystem::remove(out_file);
    filesystem::remove( log_file );

    VI res;
    for( string s : lines ) res.push_back( stoi(s) );
    return res;
}


VI DSSE::findMHSForSetsSAT(VVI &sets) {
    clog << "Solving instance using SAT" << endl;

    UniformIntGenerator rnd(0,LLONG_MAX>>2);
    int r = rnd.rand();

    string infile = "hs_sat_in.txt" + to_string(r);
    ofstream str(infile.c_str());
    int N = 0;
    for( VI & C : sets ) for( int d : C ) N = max(d,N);
    str << sets.size() << endl;
    for( VI & C : sets ){
        for(int i=0; i<C.size(); i++) {
            if(i) str << " ";
            str << C[i]+1;
        }
        str << "\n";
    }
    str.flush();
    str.close();

    string out_file = "hs_sat_out.txt" + to_string(r);
    string command = "python3 solveSAT.py < " + infile + " > " + out_file;
    auto suppress = system(command.c_str());


    VI res;
    double solve_time_millis = 0;
    {
        ifstream str( out_file );
        str >> solve_time_millis;
        int len;
        str >> len;
        if(len) res.resize(len);
        for(int i=0; i<len; i++) {
            str >> res[i];
            res[i]--;
        }
    }

    {
        clog << "Found result for instance in " << solve_time_millis / 100 << " seconds, res.size(): " << res.size() << endl;
        assert( HSLS::isCorrectHS(sets,res) );
    }

    // removing temporary files
    filesystem::remove(infile);
    filesystem::remove(out_file);



    return res;
}

VI DSSE::findMHSForSetsCPSAT(VVI &sets, int time_limit_millis, bool admit_nonexact_value) {
    if(sets.empty()) return {};
    if constexpr (enable_logs)
    clog << "Solving instance using CPSAT" << endl;
    clog << "sets.size(): " << sets.size() << endl;
    {
        unordered_set<int> zb;
        for (auto & v : sets) zb.insert(ALL(v));
        clog << "different elements: " << zb.size() << endl;
    }

    UniformIntGenerator rnd(0,LLONG_MAX>>2);
    int r = rnd.rand();
    r *= sets.size();
    for ( int i=0; i<sets.size(); i++ ) {
        for (int j=0; j<sets[i].size(); j++) r += (j+1) * sets[i][j];
        r *= (i+1);
        r++;
    }
    r = abs(r);

    string infile = "hs_cpsat_" + to_string(r) + "_in.txt";

    {
        ofstream str(infile.c_str());
        // int N = 0;
        // for( VI & C : sets ) for( int d : C ) N = max(d,N);
        str << sets.size() << "\n";
        for( VI & C : sets ){
            for(int i=0; i<C.size(); i++) {
                if(i) str << " ";
                str << C[i]+1;
            }
            str << "\n";
        }
        str << (int)ceil(time_limit_millis / 1000) << endl;
        str.flush();
        str.close();
    }

    string out_file = "hs_cpsat_" + to_string(r) + "_out.txt";
    string command = "python3 solveCPSAT.py < " + infile + " > " + out_file;

    if constexpr (enable_logs) clog << "Running command: " << command << endl;
    auto suppress = system(command.c_str());


    VI res;
    double solve_time_millis = 0;
    {
        assert(filesystem::exists(out_file));
        if( !filesystem::exists(out_file) ) exit(8);

        ifstream str( out_file );
        str >> solve_time_millis;
        // string s; str >> s; DEBUG(s);
        int len;
        str >> len;
        if(len) res.resize(len);
        for(int i=0; i<len; i++) {
            str >> res[i];
            res[i]--;
        }
    }

    {
        if constexpr (enable_logs)
        clog << "Found result for instance in " << solve_time_millis / 100 << " seconds, res.size(): " << res.size() << endl;
        if(time_limit_millis == 1e9) assert( HSLS::isCorrectHS(sets,res) );
    }

    if(time_limit_millis == 1e9) assert(!res.empty());

    // removing temporary files

    bool remove_temporary_files = true;
    if(remove_temporary_files) {
        filesystem::remove(infile);
        filesystem::remove(out_file);
    }else {
        clog << "Not removing temporary CPSAT in/out files" << endl;
    }

    if constexpr (enable_logs) clog << "Returning result found by CPSAT" << endl;

    return res;
}

VI DSSE::findMHSForSetsILPOR(VVI &sets) {
    if(sets.empty()) return {};
    if constexpr (enable_logs)
        clog << "Solving instance using ILPOR" << endl;

    UniformIntGenerator rnd(0,LLONG_MAX>>2);
    int r = rnd.rand();
    r = abs(r);

    string infile = "hs_ilpor_" + to_string(r) + "_in.txt";

    {
        ofstream str(infile.c_str());
        // int N = 0;
        // for( VI & C : sets ) for( int d : C ) N = max(d,N);
        str << sets.size() << "\n";
        for( VI & C : sets ){
            for(int i=0; i<C.size(); i++) {
                if(i) str << " ";
                str << C[i]+1;
            }
            str << "\n";
        }
        str.flush();
        str.close();
    }

    string out_file = "hs_ilpor_" + to_string(r) + "_out.txt";
    string command = "python3 solveILPOR.py < " + infile + " > " + out_file;

    if constexpr (enable_logs) clog << "Running command: " << command << endl;
    auto suppress = system(command.c_str());


    VI res;
    double solve_time_millis = 0;
    {
        assert(filesystem::exists(out_file));
        if( !filesystem::exists(out_file) ) exit(8);

        ifstream str( out_file );
        str >> solve_time_millis;
        // string s; str >> s; DEBUG(s);
        int len;
        str >> len;
        if(len) res.resize(len);
        for(int i=0; i<len; i++) {
            str >> res[i];
            res[i]--;
        }
    }

    {
        if constexpr (enable_logs)
            clog << "Found result for instance in " << solve_time_millis / 100 << " seconds, res.size(): " << res.size() << endl;
        assert( HSLS::isCorrectHS(sets,res) );
    }

    assert(!res.empty());

    // removing temporary files

    bool remove_temporary_files = true;
    if(remove_temporary_files) {
        filesystem::remove(infile);
        filesystem::remove(out_file);
    }else {
        clog << "Not removing temporary CPSAT in/out files" << endl;
    }

    if constexpr (enable_logs) clog << "Returning result found by ILPOR" << endl;

    return res;
}
