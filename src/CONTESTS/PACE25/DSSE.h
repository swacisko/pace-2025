//
// Created by sylwe on 04/05/2025.
//

#ifndef DSSE_H
#define DSSE_H

#include "DominatingSetSolver.h"
#include "Pace25Utils.h"



class DSSE {
public:

    DSSE( VVI _V, VB _hit_nodes = {}, VB _excluded_nodes = {}, VB _forbidden_nodes = {}, int _rec_depth = 0 ) {
        V = move(_V);
        hit_nodes = move(_hit_nodes);
        excluded_nodes = move(_excluded_nodes);
        forbidden_nodes = move(_forbidden_nodes);
        rec_depth = _rec_depth;
        {
            int N = V.size();
            // if( hit_nodes.empty() ) {
            //     assert( excluded_nodes.empty() );
            //     assert( forbidden_nodes.empty() );
            //     hit_nodes = VB(N);
            //     excluded_nodes = VB(N);
            //     forbidden_nodes = VB(N);
            // }

            if( hit_nodes.empty() ) hit_nodes = VB(N);
            if( excluded_nodes.empty() ) excluded_nodes = VB(N);
            if( forbidden_nodes.empty() ) forbidden_nodes = VB(N);
        }
    }

    /**
     * Finds optimum DS of a given graph [V].
     * @return
     */
    VI solve(bool add_isolated_nodes = true, bool use_reductions = true, bool consider_connected_components = true);

    VI solveIterative();

    // hs_solving_method: 0 = scipy.optimize.milp, 1 = FINDMINHS
    static VI findMHSForSets( VVI & sets, HSMethod hs_solving_method = CPSAT, int time_limit_millis = 1e9,
        VI upper_bound_solution = {}, int lower_bound = 1 );

    static VI findMHSForSetsFINDMINHS(VVI &sets, VI upper_bound_solution = {}, int lower_bound = 1);
    static VI findMHSForSetsSAT(VVI &sets);
    static VI findMHSForSetsCPSAT(VVI &sets, int time_limit_millis = 1e9, bool admit_nonexact_value = false);
    static VI findMHSForSetsILPOR(VVI &sets);


    // tuple<VB,VB,vector<LiftableRule*>> preprocessForExact();
    pair<int,vector<LiftableRule*>> preprocessForExact();

    HSMethod exact_hs_solving_method = SAT;
    int rec_depth_for_hs_solver = 0;
    int reductions_time_liimt = inf;

private:

    VVI V;
    VB hit_nodes, excluded_nodes, forbidden_nodes;

    VI createReducibleNodes( vector<LiftableRule*> & lft );

    int getNodeToBranch();
    int getNodeToBranchOld();
    VI solveForConnected(bool use_reductions = true);

    int rec_depth = 0;
    void indent(){ for(int i=0; i<rec_depth; i++) clog << ".\t"; }

    bool isCorrect(VVI &V, VI & res, VB &hit, bool disregard_isolated_nodes = true);
    void writeUnhitNodes(VVI &V, VI & res, VB &hit, bool disregard_isolated_nodes = true);
    void writeRules(vector<LiftableRule*> lft);

    // checks whether given solution [res] is a valid DS of graph [V], assuming that nodes in [hit] are hit
    // if not, it write some basic information on the instance
    bool assertCorrectnessAndWrite(VVI & V, VI & res, VB & hit, VB & exc, VB & forb, vector<LiftableRule*> lft,
        bool disregard_isolated_nodes = true);

    VI findOptimalResultsHS();

};

#endif //DSSE_H
