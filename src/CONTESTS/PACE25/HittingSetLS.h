//
// Created by sylwe on 04/03/2025.
//

#ifndef HITTINGSETLS_H
#define HITTINGSETLS_H

#include "Makros.h"
#include "Pace25Utils.h"
#include "Stopwatch.h"

class Stopwatch;

class HittingSetLS{
public:

    HittingSetLS(Stopwatch & s, VB hn) : sw(s), hit_nodes(hn) {}
    HittingSetLS( VVI sets, VI hs, VB _hit_nodes, Stopwatch & s);

    // VI hsImprovementLS2( int iters, int lower_bound = -1,
    //     int add_violation_frequency = 10000, int remove_violation_frequency = 11111 );
    // VI hsImprovementLS3( int iters, int lower_bound = -1,
    //     bool continue_until_improvement_found = false,
    //     const int add_violation_frequency = 10000, const int remove_violation_frequency = 5'111 );

    VI hsImprovementLS4( int iters, int lower_bound = -1, bool use_tabu_for_nonhs = false, bool admit_using_dynamic_sets = true );
    VI hsImprovementLS4SA( int iters, int lower_bound = -1 );

    static void trimHsToNodesInSets(VVI & sets, VI & hs);

    static void fillByHSToValidHS(VVI & sets, VI & hs );
    static VVI getUnhitSets( VVI & sets, VI& hs );
    static VVI getHitSets( VVI & sets, VI& hs );

    static int getMaxElement(VVI & sets, VI & hs) {
        assert( !sets.empty() && !hs.empty() && "make sure that this does not happen..." );
        int N = -1;
        if(!hs.empty()) N = *max_element(ALL(hs));
        for(auto & v : sets) N = max( N, *max_element(ALL(v)) );
        return N;
    }

    static bool isCorrectHS(VVI & sets, VI hs, VB & hit_nodes, int N = -1);

    static bool isCorrectHS(VVI & sets, VI hs, int N = -1) {
        if(sets.empty()) return true;
        if(N == -1) N = getMaxElement(sets,hs)+1;
        VB was(N);
        for( int v : hs ) was[v] = true;
        for( auto & v : sets ) {
            bool hit = false;
            for(int d : v) hit |= was[d];
            // if(!hit) clog << "\t!!! Set v: " << v << " is not hit by hs: " << hs << endl;
            if(!hit) return false;
        }
        return true;
    }

    static void removeUnhitSets( VVI & sets, VI & hs ) {
        if ( sets.empty() ) return;
        int N = getMaxElement(sets,hs)+1;
        VB was(N);
        for(int d : hs) was[d] = true;
        auto fun = [&](int ind) {
            return all_of( ALL(sets[ind]), [&]( int a ){ return !was[a]; } );
        };
        REMCFUN(fun, sets);
    }

    static VI bruteSmallSize( VVI & sets );

    // static void fillGreedilyToValidSolution(VVI & V, VI & hs, int K, VB & hit_nodes);

    static void removeMarkedNodes(VVI & sets, VB & mask) {
        for(auto & v : sets) REMCVAL(mask, v);
        REMCFUN( [&](int ind){ return sets[ind].empty(); }, sets );
    }

    tuple<VVI,VI,VI> simplePreprocess(VVI sets, VI hs);
    static void removeDominatingSets(VVI & sets);
    static VVI createV(VVI & sets);


    static pair<VI,VVI> hsImprovementLS(VVI sets, VI hs, VB hit_nodes, Stopwatch & sw, int iters = 1e3, int lower_bound = 1,  bool reduce = false,
                bool use_tabu_for_nonhs = false, bool admit_using_sa = true, bool admit_using_dynamic_sets = true);

    tuple<VVI,VI,VI> reduceForHSLSOld(VVI sets, VI hs);
    tuple<VVI,VI,VI> reduceForHSLS(VVI sets, VI hs);

    // int persistent_search_iterations_left = 0;

private:
    Stopwatch & sw;

    VB hit_nodes;

    VVI always_hit_sets;

    VVI V;

    VI hs;

    VB in_hs;
    VVI sets;

    int N;
    int S;

    // int uncovered_sets = 0;

    VI covered_by;
    // vector<unordered_set<int>> covered_by_nodes;
    VVI covered_by_nodes; // for most instances this is surely better...

    VLL hashes;

    IntGenerator rnd;

};
using HSLS = HittingSetLS;

#endif //HITTINGSETLS_H
