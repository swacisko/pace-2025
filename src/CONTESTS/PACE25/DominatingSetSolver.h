//
// Created by sylwe on 04/03/2025.
//

#ifndef DOMINATINGSETSOLVER_H
#define DOMINATINGSETSOLVER_H

#include <Stopwatch.h>

#include "Makros.h"
#include "DSReducer.h"
#include "Pace25Utils.h"


class DominatingSetSolver {
public:
    explicit DominatingSetSolver(Stopwatch & s, VB hn = {}, VB exc = {})
        : sw(s), hit_nodes(move(hn)), excluded_nodes(move(exc)){}

    VI solveH( VVI V, int K, bool use_preprocessing, int time_limit_millis, bool leave_at_K1 = false,
        bool recurse_on_disconnected = true );

    tuple<VI,VB,VB,VI,vector<LiftableRule*>> reductionRulesDS(VVI & V,int time_limit_millis = 1e9,
        const bool only_basic_reductions = false);

    static bool isCorrect(VVI &V, VI S, int K);
    static bool isCorrect(VVI &V, VI S, int K, VB & hit_nodes);

    VI ds21swaps( VVI & V, VI hs, double small_iters_scale = 300, int max_large_iters = 10,
                bool enable_21_swaps = false, int K = 0 );

    VI ds21swapsGRASP( VVI & V, VI hs, int K, bool use_perpetually_small_iterations = false);
    VI greedyWithReductions(VVI V);


    static void fillGreedilyToValidSolution(VVI & V, VI & ds, int K, VB & hit_nodes);

    static bool isVCCase(VVI & V, VB & hit_nodes);
    static tuple<VVI,VI,VI> transformToVC(VVI & V, VB & hit_nodes);

    int recursion_level = 0;
    // bool use_recursive_reducer = false;

    // if true, then an exact result is found instead of heuristic
    bool find_exact_result = false;

    HSMethod exact_hs_solving_method = MILP; // 0 = MILP, 1 - FINDMINHS

    static void writeUnhitNodes(VVI V, VI res, int K, VB hit_nodes);

    bool hs_track = false; // perhaps setting to true for HS track will be better ?

    void setPermanentExcludedNodeUnhitDominator(VI penud){ permanent_excluded_node_unhit_dominator = move(penud); }

    /**
     * Takes all unhit nodes and creates sets for them. For each such set creates a clique in the new graph.
     * Then for this graph finds a DS and returns it.
     */
    VI findDSOfHSGraph( VVI & V, int time_limit_millis );

// private:
    Stopwatch &sw;
    VB hit_nodes, excluded_nodes;
    VI permanent_excluded_node_unhit_dominator;

    // VI baseline0(VVI V, int K);
    VI baseline1(VVI V, int K, VI initS = {});
    VI baseline1v2(VVI V, int K);
    VI baseline2(VVI V, int K);
    VI baselineHG2(VVI V, int K);
    VI baselineHG(VVI V, int K, VI initS = {});
    VI hillClimberDS(VVI &V, VI res);
};
using DSS = DominatingSetSolver;

#endif //DOMINATINGSETSOLVER_H
