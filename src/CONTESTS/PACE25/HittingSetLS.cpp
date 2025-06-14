//
// Created by sylwe on 04/03/2025.
//

#include "HittingSetLS.h"
#include <CombinatoricUtils.h>
#include <RandomSelectionSet.h>
// #include "graphs/StaticGraph.h"

#include "CollectionOperators.h"
#include <StandardUtils.h>

#include "DominatingSetSolver.h"
#include "datastructures/Heap.h"

bool HittingSetLS::isCorrectHS(VVI & sets, VI hs, VB & hit_nodes, int N) {
    if (sets.empty()) return true;
    if(N == -1) N = getMaxElement(sets,hs)+1;
    VB was(N);
    for( int v : hs ) was[v] = true;
    for( auto & v : sets ) {
        // bool hit = false;
        // for(int d : v) hit |= was[d];
        //
        // bool all_hit = true;
        // for(int d : v) all_hit &= hit_nodes[d];
        // if(!hit && !all_hit) {
        //     // DEBUG(hit);
        //     // DEBUG(all_hit);
        //     // DEBUG(v.size());
        //     // DEBUG(v);
        //     return false;
        // }

        bool hit = false;
        bool all_hit = true;
        for(int d : v) {
            hit |= was[d];
            all_hit &= hit_nodes[d];
        }
        if(!hit && !all_hit) return false;
    }
    return true;
}


VVI HittingSetLS::createV(VVI &sets) {
    int N = 0;
    for(const auto & C : sets) for(int d : C) N = max(N,d+1);

    int S = sets.size();
    VVI V(N);

    VI degs(N,0);
    for( int i=0; i<S; i++ ) for( int d : sets[i] ) degs[d]++;
    for(int i=0; i<N; i++) if ( degs[i] ) V[i].reserve(degs[i]);

    for( int i=0; i<S; i++ ){
        for( int d : sets[i] ){
            V[d].push_back(i);
        }
    }

    return V;
}

void HittingSetLS::removeDominatingSets(VVI & sets) {
    int N = 0;
    for(const auto & C : sets) for(int d : C) N = max(N,d+1);
    int S = sets.size();

    VVI B = createV(sets);
    VI cnt(S,0);
    VB is_dominating(S);

    // for(int i=0; i<S; i++) {
    //     for( int d : sets[i] ) {
    //         for( int j : B[d] ) {
    //             cnt[j]++;
    //             if(cnt[j] == sets[j].size() && i != j) {
    //                 if( sets[i].size() > sets[j].size() || ( sets[i].size() == sets[j].size() && i < j ) ) {
    //                     is_dominating[i] = true;
    //                 }
    //             }
    //         }
    //     }
    //     for( int d : sets[i] ) for( int j : B[d] ) cnt[j] = 0;
    // }

    for(int i=0; i<S; i++) { // just a bit faster version
        for( int d : sets[i] ) {
            for(int t=0; t+1 < B[d].size(); t++) cnt[B[d][t]]++;
            int j = B[d].back();
            cnt[j]++;
            if(cnt[j] == sets[j].size() && i != j) {
                if( sets[i].size() > sets[j].size() || ( sets[i].size() == sets[j].size() && i < j ) ) {
                    is_dominating[i] = true;
                }
            }

            // for( int j : B[d] ) {
            //     cnt[j]++;
            //     if(cnt[j] == sets[j].size() && i != j) {
            //         if( sets[i].size() > sets[j].size() || ( sets[i].size() == sets[j].size() && i < j ) ) {
            //             is_dominating[i] = true;
            //         }
            //     }
            // }
        }
        for( int d : sets[i] ) for( int j : B[d] ) cnt[j] = 0;
    }

    REMCIND(is_dominating,sets);
}

void HittingSetLS::trimHsToNodesInSets(VVI & sets, VI & hs) {
    if(hs.empty()) return;
    int N = *max_element(ALL(hs))+1;
    for(auto & v : sets) N = max(N, *max_element(ALL(v))+1 );
    VB helper(N,true);
    for( const auto & v : sets ) for(int d : v) helper[d] = false;
    REMCVAL(helper,hs);
}

void HittingSetLS::fillByHSToValidHS(VVI &sets, VI &hs) {
    if (sets.empty()) return;
    int N = getMaxElement(sets,hs)+1;
    VB was(N);
    VVI unhit_sets = getUnhitSets(sets,hs);
    VI unhit_hs; unhit_hs.reserve(unhit_sets.size());
    VVI sets_always_hit;
    for(auto & v : unhit_sets) unhit_hs.push_back(v[0]);
    StandardUtils::makeUnique(unhit_hs);
    VB dummy_hit_nodes(N);
    Stopwatch sw;
    sw.setLimit("main", inf);
    sw.start("main");
    int iters = 5 * ( unhit_sets.size() + unhit_hs.size() );
    tie(unhit_hs,sets_always_hit) = hsImprovementLS(unhit_sets, unhit_hs, dummy_hit_nodes, sw, iters, 1,
        false, false, false, false );

    if constexpr (enable_logs) { DEBUG(hs.size()); DEBUG(unhit_hs.size()); DEBUG(hs.size() + unhit_hs.size()); }

    {
        auto hit_sets = getHitSets(sets,hs);
        trimHsToNodesInSets(hit_sets, hs); // fast version
        // { // slow version
        //     iters = 5 * (hit_sets.size() + hs.size());
        //     hs =  hsImprovementLS(hit_sets, hs, dummy_hit_nodes, sw, iters, 1,
        //         false, false, false, false );
        // }
    }

    hs += unhit_hs;
    assert(isCorrectHS(sets,hs));

    iters = 5*(sets.size() + hs.size());
    tie(hs,sets_always_hit) = hsImprovementLS(sets, hs, dummy_hit_nodes, sw, iters, 1,
        false, false, false, false );

    assert(isCorrectHS(sets,hs));
}

VVI HittingSetLS::getUnhitSets( VVI & sets, VI& hs ) {
    if ( sets.empty() ) return {};
    int N = getMaxElement(sets,hs)+1;
    VB was(N);
    for(int d : hs) was[d] = true;
    VVI unhit;
    for(const auto & v : sets) {
        bool hit = false;
        for(int d : v) hit |= was[d];
        if(!hit) unhit.push_back(v);
    }
    return unhit;
}

VVI HittingSetLS::getHitSets( VVI & sets, VI& hs ) {
    if (sets.empty()) return {};
    int N = getMaxElement(sets,hs)+1;
    VB was(N);
    for(int d : hs) was[d] = true;
    VVI hit_sets;
    hit_sets.reserve(sets.size());
    for(const auto & v : sets) {
        bool hit = false;
        for(int d : v) hit |= was[d];
        if(hit) hit_sets.push_back(v);
    }
    return hit_sets;
}

HittingSetLS::HittingSetLS(VVI sets, VI hs, VB _hit_nodes, Stopwatch & s) : sw(s)
{
    this->hit_nodes = std::move(_hit_nodes);

    for( auto & v : sets ) sort(ALL(v));
    // {
    //     int opt = ( sets.size() % 4 );
    //     if(opt == 0) sort(ALL(sets), [&](auto & v, auto & w){ return v.size() < w.size(); });
    //     if(opt == 1) sort(ALL(sets), [&](auto & v, auto & w){ return v.size() > w.size(); });
    //     if(opt == 2) StandardUtils::shuffle(sets);
    //     if(opt == 3) {}
    // }
    {
        IntGenerator rnd;
        int opt = rnd.nextInt(6);
        if(opt == 0) sort(ALL(sets), [&](auto & v, auto & w){ return v.size() < w.size(); });
        if(opt == 1) sort(ALL(sets), [&](auto & v, auto & w){ return v.size() > w.size(); });
        // if(opt == 2) StandardUtils::shuffle(sets);
        if(opt == 2) shuffle(sets,rnd);
        if(opt == 3) for( auto & v : sets ) reverse(ALL(v));
        if(opt == 4) for( auto & v : sets ) if( rnd.nextInt(2) ) reverse(ALL(v));
        if(opt == 5) {}

        if( opt <= 2 && rnd.nextInt(5) == 0 ) {
            for( auto & v : sets ) if( rnd.nextInt(2) ) reverse(ALL(v));
        }

        if( rnd.nextInt(4) == 0 ) shuffle(sets,rnd); // #TEST
    }
    // this->sets = sets;
    // this->hs = hs;

    N = 0;
    for(const auto & C : sets) for(int d : C) N = max(N,d+1);
    assert(!sets.empty());
    assert(N > 0);

    S = sets.size();
    V = VVI(N); // V[i] is the list of ids of sets that contain node i

    {
        VI degs(N,0);
        for( int i=0; i<S; i++ ) for( int d : sets[i] ) degs[d]++;
        for(int i=0; i<N; i++) if (degs[i]) V[i].reserve(degs[i]);
    }

    for( int i=0; i<S; i++ ){
        for( int d : sets[i] ){
            V[d].push_back(i);
        }
    }

    { // #TEST
        // for(auto & v : this->sets) StandardUtils::shuffle(v);
        // for(auto & v : V) StandardUtils::shuffle(v);
    }

    hashes = VLL(N);
    for(int i=0; i<N; i++) hashes[i] = rnd.rand();

    swap(this->sets, sets);
    swap(this->hs,hs);
}

//
// void HittingSetLS::fillGreedilyToValidSolution(VVI & V, VI &hs, int K, VB &hit_nodes) {
//     int N = V.size();
//     VB was(N);
//     VI dst(N,inf);
//     auto reachable = findReachableNodesFromSWithinDistanceK(V, hs, K, dst,was );
//
//     VB hit(N);
//     for(int d : reachable) hit[d] = true;
//     VI perm = CombinatoricUtils::getRandomPermutation(N);
//
//     int block_size = 5;
//     VI to_add;
//     auto addNodes = [&]() {
//         reachable = findReachableNodesFromSWithinDistanceK( V, to_add, K, dst,was );
//         hs += to_add;
//         to_add.clear();
//         for(int d : reachable) hit[d] = true;
//     };
//     for( int d : perm ) if(!hit[d] && !hit_nodes[d]) {
//         to_add.push_back(d);
//         if( (to_add.size() % block_size == 0) ) addNodes();
//     }
//     if(!to_add.empty()) addNodes();
// }

tuple<VVI,VI,VI> HittingSetLS::simplePreprocess(VVI sets, VI hs) {
    if( sets.empty() || hs.empty() ) return {sets, hs, {}};

    int N = *max_element(ALL(hs)) + 1;
    for(VI & C : sets) for(int d : C) N = max(N,d+1);

    // for( auto & v : sets ) StandardUtils::shuffle(v);

    constexpr bool check_assertions = false;
    assert(HittingSetLS::isCorrectHS(sets, hs,  hit_nodes));

    VI kernel;
    VB was(N);
    VB was2(N);
    // VLL hashes(N);
    VLL hashes1(N), hashes2(N), hashes3(N);

    IntGenerator rnd;
    // bool changes = (rnd.nextInt(2) == 0);
    bool changes = true;
    if(changes) {
        UniformIntGenerator rnd2(0, LLONG_MAX);
        // for(int i=0; i<N; i++) hashes[i] = rnd.rand();
        // for(int i=0; i<N; i++) hashes1[i] = (1 + rnd.rand()) * (1 + rnd.rand());
        for(int i=0; i<N; i++) hashes1[i] = (LL)rnd2.rand();
        for(int i=0; i<N; i++) hashes2[i] = (LL)rnd2.rand();
        for(int i=0; i<N; i++) hashes3[i] = (LL)rnd.rand();
        for( int i=0; i<N; i++ ) {
            while( hashes1[i] == 0 ) hashes1[i] = rnd2.rand();
            while( hashes2[i] == 0 ) hashes2[i] = rnd2.rand();
            while( hashes3[i] == 0 ) hashes3[i] = rnd.rand();
        }
        // for( auto & v : sets ) StandardUtils::shuffle(v);
    }


    auto makeUnique = [&](VI & v) {
        for( int i=(int)v.size()-1; i>=0; i-- ) {
            int w = v[i];
            if(was2[w]){ REM(v,i); }
            was2[w] = true;
        }
        for(int d : v) was2[d] = false;
    };

    auto removeDuplicateSets = [&]() {
        // unordered_set<PLL, pairhash> zb;
        // set<PLL> zb;
        set<pair<PLL,PLL>> zb;
        // zb.reserve(sets.size());
        for( int i=(int)sets.size()-1; i>=0; i-- ) {
            assert(!sets[i].empty());
            if(sets[i].empty()){ REM(sets,i); continue; }
            // LL h = 0;
            LL h1 = 0, h2 = 0, h3 = 0, h4 = 0;
            makeUnique(sets[i]);
            // for( auto d : sets[i] ) h ^= hashes[d];
            for( auto d : sets[i] ) {
                h1 ^= hashes1[d];
                h2 ^= hashes2[d];
                h3 ^= hashes3[d];
                h4 ^= (hashes1[d] + hashes2[d]) ^ hashes3[d];
            }
            // if( zb.contains(h) ) REM(sets,i);
            // zb.insert(h);
            // if( zb.contains({h1,h2}) ) REM(sets,i);
            // zb.insert({h1,h2});
            if( zb.contains({{h1,h2},{h3,h4}}) ) REM(sets,i);
            zb.insert({{h1,h2},{h3,h4}});
        }
    };

    auto init_sets = sets;
    auto init_hs = hs;
    int init_N = N;

    while(changes){ // this is valid preprocessing - can be used before starting any computation
        changes = false;
        int total_elements = SUMSIZES(sets);
        // clog << "sets: " << endl; for(auto & v : sets) DEBUG(v);
        // DEBUG(total_elements); ENDL(1);


        // // fill(ALL(was),false);
        removeDuplicateSets();

        if constexpr (check_assertions) if(!HittingSetLS::isCorrectHS(sets, hs, hit_nodes)) {
            if constexpr (enable_logs) {
                clog << "sets: " << endl; for(auto & v : sets){ sort(ALL(v)); DEBUG(v);}
                DEBUG(hs);
                DEBUG(kernel);
            }
            assert(HittingSetLS::isCorrectHS(sets, hs, hit_nodes));
        }

        VI cnt(N,0);
        for( auto & v : sets ) for(int d : v) cnt[d]++;
        VB in_hs(N);
        for(int d : hs) in_hs[d] = true;
        for( int j = (int)sets.size()-1; j>=0; j-- ) {
            auto & v = sets[j];
            for(int i=(int)v.size()-1; i>=0; i--) if( cnt[v[i]] == 1 && v.size() >= 2 ) {
                int w = v[i];
                // clog << "Removing " << w << " from v: " << v << endl;
                if( in_hs[w] && !was[w] ) {
                    kernel.push_back(w);
                    was[w] = true;
                }
                if( in_hs[w] ) {
                    REM(sets,j);
                    break;
                }
                REM(v,i);
            }
        }

        if constexpr (check_assertions) if(!HittingSetLS::isCorrectHS(sets, hs, hit_nodes)) {
            if constexpr (enable_logs) {
                clog << "sets: " << endl; for(auto & v : sets){ sort(ALL(v)); DEBUG(v);}
                DEBUG(hs);
                DEBUG(kernel);
            }
            assert(HittingSetLS::isCorrectHS(sets, hs, hit_nodes));
        }

        for(int d : kernel) was[d] = true;
        for( auto & v : sets ) if( v.size() == 1 ) {
            int w = v[0];
            if(!was[w]) {
                // clog << "Adding w: " << w << " to kernel" << endl;
                kernel.push_back(w);
                was[w] = true;
            }
        }

        if constexpr (check_assertions) if(!HittingSetLS::isCorrectHS(sets, hs, hit_nodes)) {
            if constexpr (enable_logs) {
                clog << "sets: " << endl; for(auto & v : sets){ sort(ALL(v)); DEBUG(v);}
                DEBUG(hs);
                DEBUG(kernel);
            }
            assert(HittingSetLS::isCorrectHS(sets, hs, hit_nodes));
        }

        // DEBUG(kernel);
        for( int i=(int)sets.size()-1; i>=0; i-- ) {
            bool hit_by_kernel = false;
            for(int d : sets[i]) hit_by_kernel |= was[d];
            if(hit_by_kernel) {
                // clog << "Removing set " << sets[i] << " as hit" << endl;
                // for(int d : sets[i]) if(!was[d]){ was[d] = true; kernel.push_back(d); } // #TEST
                REM(sets,i);
            }
        }


        if constexpr (check_assertions) if(!HittingSetLS::isCorrectHS(sets, hs, hit_nodes)) {
            if constexpr (enable_logs) {
                clog << "sets: " << endl; for(auto & v : sets){ sort(ALL(v)); DEBUG(v);}
                DEBUG(hs);
                DEBUG(kernel);
            }
            assert(HittingSetLS::isCorrectHS(sets, hs, hit_nodes));
        }

        if constexpr (check_assertions) assert(HittingSetLS::isCorrectHS(init_sets, hs + kernel, hit_nodes));

        REMCVAL(was,hs);

        if constexpr (check_assertions) if(!HittingSetLS::isCorrectHS(sets, hs, hit_nodes)) {
            if constexpr (enable_logs) {
                clog << "sets: " << endl; for(auto & v : sets){ sort(ALL(v)); DEBUG(v);}
                DEBUG(hs);
                DEBUG(kernel);
            }
            assert(HittingSetLS::isCorrectHS(sets, hs+kernel, hit_nodes));
            assert(HittingSetLS::isCorrectHS(sets, hs, hit_nodes));
        }


        if constexpr (check_assertions) assert(HittingSetLS::isCorrectHS(init_sets, hs + kernel, hit_nodes));
       // removeDominatingSets(sets); // this is too time-consuming to do it here...

        // DEBUG(hs);
        if(!hs.empty()) HittingSetLS::trimHsToNodesInSets(sets,hs);

        if constexpr (check_assertions) if(!HittingSetLS::isCorrectHS(sets, hs, hit_nodes)) {
            if constexpr (enable_logs) {
                clog << "sets: " << endl; for(auto & v : sets){ sort(ALL(v)); DEBUG(v);}
                DEBUG(hs);
                DEBUG(kernel);
            }
            assert(HittingSetLS::isCorrectHS(sets, hs, hit_nodes));
        }

        changes = (total_elements != SUMSIZES(sets));

        if constexpr (check_assertions) assert(HittingSetLS::isCorrectHS(init_sets, hs + kernel, hit_nodes));
    }

    // removeDuplicateSets();

    if(!HittingSetLS::isCorrectHS(init_sets, hs + kernel, hit_nodes)) {
        if constexpr (enable_logs) {
            DEBUG(init_N);
            DEBUG(init_sets);
            DEBUG(init_hs);
            DEBUG(kernel);
            DEBUG(sets);
            DEBUG(hs);
        }
        assert( set(ALL(hashes1)).size() == hashes1.size() );
        assert( set(ALL(hashes2)).size() == hashes2.size() );
        assert(HittingSetLS::isCorrectHS(init_sets, hs + kernel, hit_nodes));
    }

    return {sets, hs, kernel};
}

VI HittingSetLS::bruteSmallSize( VVI & sets ) {
    int N = 0;

    for ( int i=0; i<N; i++ ) {
        bool all_hit = true;
        for ( auto & zb : sets ) {
            bool h = false;
            for (int d : zb) h |= (d == i);
            if (!h){ all_hit = false; break; }
        }
        if (all_hit) return {i};
    }

    if ( N >= 2 )
    for ( int i=0; i<N; i++ ) for (int j=i+1; j<N; j++) {
        bool all_hit = true;
        for ( auto & zb : sets ) {
            bool h = false;
            for (int d : zb) h |= ((d == i) || (d == j));
            if (!h){ all_hit = false; break; }
        }
        if (all_hit) return {i,j};
    }

    if ( N >= 3 )
    for ( int i=0; i<N; i++ ) for (int j=i+1; j<N; j++) for ( int k=j+1; k<N; k++ ) {
        bool all_hit = true;
        for ( auto & zb : sets ) {
            bool h = false;
            for (int d : zb) h |= ((d == i) || (d == j) || (d == k));
            if (!h){ all_hit = false; break; }
        }
        if (all_hit) return {i,j,k};
    }

    if ( N >= 4 )
    for ( int i=0; i<N; i++ ) for (int j=i+1; j<N; j++) for ( int k=j+1; k<N; k++ ) for (int l=k+1; l<N; l++) {
        bool all_hit = true;
        for ( auto & zb : sets ) {
            bool h = false;
            for (int d : zb) h |= ((d == i) || (d == j) || (d == k) || (d == l));
            if (!h){ all_hit = false; break; }
        }
        if (all_hit) return {i,j,k,l};
    }

    return {};
}

VI HittingSetLS::hsImprovementLS4( const int _iters, const int lower_bound,
    const bool use_tabu_for_nonhs, const bool admit_using_dynamic_sets) {

    if(sets.empty()) return {};
    if(sets.size() == 1) return { sets[0][rnd.nextInt(sets[0].size())] };
    if ( sets.size() == 2 ) {
        VB was(N);
        for (int d : sets[0]) was[d] = true;
        for ( int d : sets[1] ) if (was[d]) return {d};
        return { sets[0][0], sets[1][0] };
    }
    if(hs.empty() || sw.tle()) return hs;
    if ( N <= 15 ) {
        auto small_res = bruteSmallSize(sets);
        if ( !small_res.empty() ) return small_res;
    }

    for ( int d : hs ) assert(d < N);

    // const int iters = min( _iters, 3'000'000 );
    const int iters = min( _iters, 30 * (N+S) );

    constexpr bool use_visited_states = true;

    int valid_hs_mask_replaced_times = 0;
    int last_valid_state_size = hs.size();
    constexpr int valid_solution_replacement_frequency = inf;
    int latest_replacement = 0;

    //*************************************
    // const bool use_dynamic_sets = (rnd.nextInt(3) == 0)
    // // // const bool use_dynamic_sets = (rnd.nextInt(2) == 0)
    // && (sets.size() >= 30) && admit_using_dynamic_sets;
    constexpr bool use_dynamic_sets = false && admit_using_dynamic_sets;

    int set_addition_frequency = 50;
    // int set_addition_frequency = 100;
    const int sets_to_remove = min( (iters/4)/set_addition_frequency, (int)(0.2 * sets.size()) );
    if(sets_to_remove) set_addition_frequency = (iters/4) / sets_to_remove;
    int set_addition_iter = 0;
    VVI removed_sets;
    deque<int> nodes_to_add_back;
    if constexpr (enable_logs) DEBUG(use_dynamic_sets);
    // if constexpr (use_dynamic_sets) if(sets_to_remove > 0) {
    if (use_dynamic_sets) if(sets_to_remove > 0) {
        removed_sets.reserve(sets_to_remove);
        for(int i=0; i<sets_to_remove; i++) {
            auto zb = sets.back();
            removed_sets.emplace_back( zb );
            sets.pop_back();
        }

        VB was(S);
        for(int i=S-sets_to_remove; i < S; i++) was[i] = true;
        for( auto & v : V ) REMCVAL(was,v);
        for(auto & v : V) for( int d : v ) assert(d < sets.size());

        // StandardUtils::shuffle(removed_sets);
        shuffle(removed_sets,rnd);
        if constexpr (enable_logs) DEBUG(sets_to_remove);
        if constexpr (enable_logs) DEBUG(set_addition_frequency);
        if constexpr (enable_logs) clog << "removed_sets.size(): " << removed_sets.size() << endl;
    }
    //*************************************

    int uncovered = 0;
    in_hs = StandardUtils::toVB(N, hs);
    VI valid_hs = hs;
    VI init_hs = hs;
    int current_state_size = hs.size();
    VB valid_hs_mask = in_hs;


    // ******************************************** uncomment to use StaticGraph structure
    // // sorting neighborhoods might exhibit more 'linear' access order in some cases, but negates variability used
    // // in HSLS constructor
    // constexpr bool sort_neighborhoods = false;
    // StaticGraph V(this->V,sort_neighborhoods);
    // ******************************************** uncomment to use StaticGraph structure


    // const int MAX_TIMESTAMP_DIFF = 5 * hs.size();
    const int MAX_TIMESTAMP_DIFF = inf;

    constexpr int EQUAL_TIMESTAMP_SPAN = 50; // 30 seems to work well for 095
    // const int EQUAL_TIMESTAMP_SPAN = 1 + rnd.nextInt(30); // 30 seems to work well for 095
    constexpr bool use_timestamps = true;
    VI timestamp;
    if constexpr (use_timestamps) timestamp = VI(N,0);

    const bool admit_neighborhood_removal = (rnd.nextInt(2) == 0); // set this to use neighborhood removal...
    // const bool admit_neighborhood_removal = false;

    constexpr bool use_visit_frequencies = true;
    // constexpr double VISIT_FREQUENCIES_COEF = 3;
    const double VISIT_FREQUENCIES_COEF = 1.05 + 1.0 * rnd.nextInt(50) / 50;
    // VI visit_frequencies;
    using VUS = vector<unsigned short>;

    // VUS visit_frequencies_rem, visit_frequencies_add;
    // if constexpr (use_visit_frequencies) visit_frequencies_rem = visit_frequencies_add = VUS(N,1);
    int visit_frequencies_counter = 0;
    VUS visit_frequencies_rem(N,1);
    VUS & visit_frequencies_add = visit_frequencies_rem;

    // covered_by[i] is the number of elements from current hitting set that belong to sets[i]
    covered_by = VI(S,0);
    covered_by_nodes.resize(S);
    LL total_cbn_remove_size = 0;
    int total_cbn_iters = 0;

    for( int v : hs ) for( int d : V[v] ) {
        covered_by[d]++;
        covered_by_nodes[d].push_back(v);
    }
    for( int i=0; i<sets.size(); i++ ) if( covered_by[i] == 0 ) uncovered++;
    assert((uncovered == 0) && "Provided hs for improvement is not valid");


    // const int LAST_FORBIDDEN_STATES_TO_KEEP = min(iters,3'000'000); // keep track of at most 10k states
    const int LAST_FORBIDDEN_STATES_TO_KEEP = min(iters,30'000); // keep track of at most 10k states
    // const int LAST_FORBIDDEN_STATES_TO_KEEP = iters; // keep track of all states
    const bool use_bloom_filter = ( LAST_FORBIDDEN_STATES_TO_KEEP <= 300'000 );
    // const bool use_bloom_filter = false;

    deque<ULL> last_states;
    last_states.resize( 2*LAST_FORBIDDEN_STATES_TO_KEEP + 10 );
    last_states.clear();


    BloomFilter visited_states_bloom(64);
    // if(use_bloom_filter) visited_states_bloom = BloomFilter( 64ll * iters ); // original
    // if(use_bloom_filter) visited_states_bloom = BloomFilter( 32ll * iters ); // smaller, bit faster
    if(use_bloom_filter) visited_states_bloom = BloomFilter( 64ll * LAST_FORBIDDEN_STATES_TO_KEEP );

    unordered_set<ULL> visited_states_set; // this is much faster if the number of iterations is very high...
    // if(!use_bloom_filter) visited_states_set.reserve( 2.5 * iters ); // each iteration creates two new states
    if(!use_bloom_filter) visited_states_set.reserve( 2.5 * LAST_FORBIDDEN_STATES_TO_KEEP ); // each iteration creates two new states
    LL current_state_hash = 0;
    for(int d : hs) current_state_hash ^= hashes[d];


    auto markVisitedState = [&](const ULL h){
        last_states.push_back(current_state_hash);

        if(use_bloom_filter) visited_states_bloom.insert(h);
        // if(use_bloom_filter) visited_states_bloom.insertHalf(h);
        else visited_states_set.insert(h);
    };

    auto isForbiddenState = [&](const ULL h) {
        if(use_bloom_filter) return visited_states_bloom.contains(h);
        // if(use_bloom_filter) return visited_states_bloom.containsHalf(h);
        else return visited_states_set.contains(h);
    };


    auto removeOldForbiddenStates = [&]() {
        if( use_bloom_filter ) {
            if( last_states.size() > 2*LAST_FORBIDDEN_STATES_TO_KEEP ) {
                visited_states_bloom.clear();
                while( last_states.size() > LAST_FORBIDDEN_STATES_TO_KEEP ) {
                    auto s = last_states.front();
                    last_states.pop_front();
                    visited_states_bloom.insert(s);
                }
            }
        }else {
            while( last_states.size() > LAST_FORBIDDEN_STATES_TO_KEEP ) {
                auto s = last_states.front();
                last_states.pop_front();
                visited_states_set.erase(s);
            }
        }
    };


    if constexpr (use_visited_states) markVisitedState(current_state_hash);


    VVI neigh_via_deg2_sets(N);
    for( int i=0; i<N; i++ ) {
        for(int d : V[i]) if( sets[d].size() == 2 ) {
            for(int dd : sets[d]) if(dd != i) neigh_via_deg2_sets[i].push_back(dd);
        }
        StandardUtils::makeUnique(neigh_via_deg2_sets[i]);
    }


    VI perm = CombinatoricUtils::getRandomPermutation(N);

    if constexpr (enable_logs) DEBUG(N);
    if constexpr (enable_logs) DEBUG(S);
    if constexpr (enable_logs) DEBUG(iters);
    int total_elements_in_sets = accumulate(ALL(sets),0, [](int s, auto & v){return s + v.size();});
    if constexpr (enable_logs) DEBUG(total_elements_in_sets);


    constexpr bool use_cc = true; // original value = true
    bool use_cc_for_hs_nodes = false;
    bool use_cc_for_nonhs_nodes = false;

    bool allow_to_add_back_only_uncovered_cost_nodes = false; // original
    int ucn_alternation_counter = 0;
    int ucn_alternation_countdown_marker = 0;
    const int ZERO_COST_VIOLATION_FREQENCY = 1 + (iters / 6); // original
    // const int ZERO_COST_VIOLATION_FREQENCY = 1 + (iters / 11); // #TEST

    // int ucn_alternation_counter = 1; // disable using this...
    // const int ZERO_COST_VIOLATION_FREQENCY = inf; // disable using this...

    // int ucn_alternation_counter = 1;
    // const int ZERO_COST_VIOLATION_FREQENCY = inf; // #use almost only ZERO COST

    VB conf_check(N, true);
    auto cmp_cc = [&]( int a, int b ) { return (bool)conf_check[b]; };

    bool use_hsn_que = false;
    deque<int> hsn_que;
    VB in_hsn_que(N);

    VI hits_uncovered(N,0); // number of uncovered sets that node hits
    // for( int i=0; i<S; i++ ){ if(covered_by[i] == 0) for(int d : sets[i]) hits_uncovered[d]++; }
    for( int i=0; i<sets.size(); i++ ) assert(covered_by[i] > 0);
    for( int i=0; i<sets.size(); i++ ){ if(covered_by[i] == 0) for(int d : sets[i]) hits_uncovered[d]++; } // #TEST


    VI all_nodes(N);
    iota(ALL(all_nodes),0);


    int iteration_counter = 0;
    // int MAX_RANDOM_MOVE_COUNTER_VALUE = iters / 2;
    const int MAX_RANDOM_MOVE_COUNTER_VALUE = iters / 4;
    auto isRandomMoveCounterInValidInterval = [&]() {
        return iteration_counter <= MAX_RANDOM_MOVE_COUNTER_VALUE;
    };

    // int MIN_NODE_FREEZE_TIME = min(1 + (int)rnd.nextInt(15), iters/100);
    int NODE_FREEZE_TIME = min(100, (int)hs.size()/2);
    // int NODE_FREEZE_TIME = min(50, (int)hs.size()/2); // 50 seems to work ok
    // int NODE_FREEZE_TIME = hs.size()/4;
    const int END_NODE_FREEZE_TIME = 1;
    constexpr int NODE_FREEZE_CHANGE_STEP = -1;
    const int NODE_FREEZE_TIME_CHANGE_FREQUENCY = 1 + 0.75 * (iters * abs(NODE_FREEZE_CHANGE_STEP)) / abs( END_NODE_FREEZE_TIME - NODE_FREEZE_TIME );
    // constexpr int NODE_FREEZE_PROBAB = 15; // from 0 to 100
    // constexpr int NODE_FREEZE_PROBAB = 25; // from 0 to 100, works ok
    // constexpr int NODE_FREEZE_PROBAB = 33; // from 0 to 100, works ok
    const int NODE_FREEZE_PROBAB = 20 + rnd.nextInt(21); // from 0 to 100

    VB frozen(N);
    // const int MIN_NODE_FREEZE_TIME = min(50, iters/100);
    // const int MIN_NODE_FREEZE_TIME = min( 30, iters/100 );
    // const int MIN_NODE_FREEZE_TIME = min(300, iters/100);
    // const int MIN_NODE_FREEZE_TIME = min( 0.1 * hs.size(), iters/100.0 );
    auto isFrozen = [&](int a) {
        if(abs(iteration_counter - timestamp[a]) > NODE_FREEZE_TIME) frozen[a] = false;
        return (bool)frozen[a];
    };

    VI covers_alone(N,0); // the number of sets that a node covers ALONE (without any other node)
    for( int i=0; i<sets.size(); i++ ){ if(covered_by[i] == 1) for( int d : sets[i] ) if(in_hs[d]) covers_alone[d]++; }
    auto cmp_hs = [&]( const int a, const int b ){
        // if constexpr( use_cc && use_cc_for_hs_nodes ) if( conf_check[a] != conf_check[b] ) return !cmp_cc(a,b);
        // if constexpr (use_cc) if( use_cc_for_hs_nodes ) if( conf_check[a] != conf_check[b] ) return !cmp_cc(a,b);


        // if (isRandomMoveCounterInValidInterval()) {
        //     // return (perm[a]+1) * covers_alone[a] < (perm[b]+1) * covers_alone[b];
        //     // return (visit_frequencies_rem[a]+1) * covers_alone[a] < (visit_frequencies_rem[b]+1) * covers_alone[b];
        //     // return (timestamp[a]+1) * covers_alone[a] < (timestamp[b]+1) * covers_alone[b];
        //     // return visit_frequencies_rem[a] < visit_frequencies_rem[b];
        //     return timestamp[a] < timestamp[b];
        //     // return perm[a] > perm[b];
        // }

        // if(hits_uncovered[a] + covers_alone[a] != hits_uncovered[b] + covers_alone[b])
        //     return hits_uncovered[a] + covers_alone[a] < hits_uncovered[b] + covers_alone[b];

        // if (isRandomMoveCounterInValidInterval()) {
        //     if( isFrozen(a) && !isFrozen(b) ) return false;
        //     if( isFrozen(b) && !isFrozen(a) ) return true;
        // }
        // if (isRandomMoveCounterInValidInterval()) {
        //     // return 1.0 * covers_alone[a] / V[a].size() < 1.0 * covers_alone[b] / V[b].size();
        //     // return covers_alone[a] * V[b].size() < covers_alone[b] * V[a].size();
        //     return covers_alone[a] - (int)V[a].size() < covers_alone[b] - (int)V[b].size();
        // }

        // if (isRandomMoveCounterInValidInterval()) {
            // if( isFrozen(a) && !isFrozen(b) ) return false;
            // if( isFrozen(b) && !isFrozen(a) ) return true;
        // }

        if( covers_alone[a] != covers_alone[b] ) return covers_alone[a] < covers_alone[b];

        // if (isRandomMoveCounterInValidInterval()) if( isFrozen(a) != isFrozen(b) ) return (bool)isFrozen(b);
        // if (isRandomMoveCounterInValidInterval()) return timestamp[a] < timestamp[b];

        if constexpr (use_timestamps) if ( abs(timestamp[a] - timestamp[b]) > EQUAL_TIMESTAMP_SPAN ) {
            return timestamp[a] < timestamp[b]; // take the oldest node
        }
        if constexpr (use_visit_frequencies) {
            // int vfa = visit_frequencies[a], vfb = visit_frequencies[b];
            int vfa = visit_frequencies_rem[a], vfb = visit_frequencies_rem[b];
            double r = 1.0 * vfa / vfb;
            if( r < 1.0/VISIT_FREQUENCIES_COEF || r > VISIT_FREQUENCIES_COEF ) {
                // return vfa > vfb; // counterintuitively: select the node that was selected most often - seems to work better
                return vfa < vfb; // better node is the one that was selected less often
            }
        }
        return perm[a] > perm[b];
    };
    Heap<int> hs_nodes( all_nodes,cmp_hs);
    for( int i=0; i<N; i++ ) if(!in_hs[i]) hs_nodes.removeFromHeap(i);

    constexpr bool use_hsn_updates_instead_of_rem_add = false; // original value = false
    // const bool use_hsn_updates_instead_of_rem_add = rnd.nextInt(2); // #TEST #CAUTION
    VI covers_alone_diff;
    if constexpr (use_hsn_updates_instead_of_rem_add) covers_alone_diff = VI(N,0);
    // if (use_hsn_updates_instead_of_rem_add) covers_alone_diff = VI(N,0);


    constexpr bool create_cc_neighborhoods = true;
    VVI cc_mark_neighborhoods;
    if constexpr( create_cc_neighborhoods ) {
        cc_mark_neighborhoods.resize(N);

        constexpr int MAX_NEIGH_SIZE = 30; // set to inf to create full structure
        constexpr int MAX_TEMP_SIZE = 300; // set to inf to create full structure

        VB was(N);
        VI temp; temp.reserve(N);
        for ( int v=0; v<N; v++ ) if( V[v].size() <= MAX_NEIGH_SIZE ) {
            temp.clear();
            for ( int d : V[v] ) if( sets[d].size() <= MAX_TEMP_SIZE ){
                for ( int u : sets[d] ) if (!was[u]) {
                    was[u] = true;
                    temp.push_back(u);
                    if(temp.size() > MAX_TEMP_SIZE) break;
                }
                if(temp.size() > MAX_TEMP_SIZE) break;
            }
            if( temp.size() <= MAX_TEMP_SIZE ) {
                sort(ALL(temp));
                cc_mark_neighborhoods[v] = temp;
            }
            for (int d : temp) was[d] = false;
        }

        // // now just for check...
        // LL total_cc_mark_neighbors_size = 0;
        // for(auto & v : cc_mark_neighborhoods) total_cc_mark_neighbors_size += v.size();
        // if(total_cc_mark_neighbors_size > 1e6) {
        //     int empty_cc_lists = 0;
        //     for(auto & v : cc_mark_neighborhoods) empty_cc_lists += v.empty();
        //     cout << "c N: " << N << ", S: " << S << ", total_cc_mark_neighbors_size: "
        //          << total_cc_mark_neighbors_size << ", \tempty_cc_lists: " << empty_cc_lists << endl;
        // }
    }

    LL mark_cc_diversification_iters = 0;

    auto mark_cc = [&]( int v ) {
        if constexpr (!use_cc) return;
        if( !use_cc_for_hs_nodes && !use_cc_for_nonhs_nodes ) return;

        bool normal_iterate = true;
        if constexpr( create_cc_neighborhoods ) if( !cc_mark_neighborhoods[v].empty() ) normal_iterate = false;

        if(normal_iterate) {
            for( int d : V[v] ) for( int u : sets[d] ) conf_check[u] = true; // original
            // for( int d : V[v] ) for( int u : sets[d] ) conf_check[u] = ( rnd.nextInt(3) > 0 ); // #TEST
            // for( int d : V[v] ) for( int u : sets[d] ) conf_check[u] = (mark_cc_diversification_iters++ & 1);
            // for( int d : V[v] ) for( int u : sets[d] ) conf_check[u] = (mark_cc_diversification_iters++ & 3); // #TEST
            // for( int d : V[v] ) for( int u : sets[d] ) conf_check[u] = (mark_cc_diversification_iters++ & 7);
            // for( int d : V[v] ) for( int u : sets[d] ) conf_check[u] = (mark_cc_diversification_iters++ & 15);
        }else {
            // iterate using preprocessed cc_mark_neighborhoods structure
            for ( int u : cc_mark_neighborhoods[v] ) conf_check[u] = true; // original
            // for ( int u : cc_mark_neighborhoods[v] ) conf_check[u] = ( rnd.nextInt(3) > 0 ); // #TEST
            // for ( int u : cc_mark_neighborhoods[v] ) conf_check[u] = (mark_cc_diversification_iters++ & 1);
            // for ( int u : cc_mark_neighborhoods[v] ) conf_check[u] = (mark_cc_diversification_iters++ & 3); // #TEST
            // for ( int u : cc_mark_neighborhoods[v] ) conf_check[u] = (mark_cc_diversification_iters++ & 7);
            // for ( int u : cc_mark_neighborhoods[v] ) conf_check[u] = (mark_cc_diversification_iters++ & 15);
        }

        conf_check[v] = false;
    };


    VI & state_change_history = all_nodes;
    state_change_history.clear();
    state_change_history.reserve(2*iters);
    VB valid_state_change_history_marker;
    valid_state_change_history_marker.reserve(2*iters);
    auto addStateChangeToHistory = [&](int v) {
        state_change_history.push_back(v);
        valid_state_change_history_marker.push_back(false);
        // if(uncovered == 0 && removed_sets.empty()) valid_state_change_history_marker.back() = true; // #TEST
    };
    auto changeInitHsToLastValidHs = [&]() {
        int ind = -1;
        // if constexpr (use_dynamic_sets){
        if (use_dynamic_sets){
            VB res(N);
            for(int d : init_hs) res[d] = true;
            int res_size = init_hs.size();
            int min_res_size = res_size;
            assert(state_change_history.size() == valid_state_change_history_marker.size());

            for( int i=0; i<valid_state_change_history_marker.size(); i++ ){
                int v = state_change_history[i];
                if(res[v]) res_size--;
                else res_size++;
                res[v] = !res[v];
                if(valid_state_change_history_marker[i] && res_size <= min_res_size) {
                    ind = i;
                    min_res_size = min(min_res_size, res_size);
                }
            }
        }else {
            for( int i=0; i<valid_state_change_history_marker.size(); i++ ){
                if(valid_state_change_history_marker[i]) ind = i;
            }
        }
        VB res(N);
        for(int d : init_hs) res[d] = true;
        for( int i=0; i<=ind; i++ ){ int v = state_change_history[i]; res[v] = !res[v]; }
        return StandardUtils::toVI(res);
    };

    if constexpr (enable_logs) {
        ENDL(1);
        DEBUG(hs.size());
        DEBUG(lower_bound);
        ENDL(1);
    }

    if(sw.tle()) return hs;

    // VI hits_uncovered(N,0); // number of uncovered sets that node hits
    // // for( int i=0; i<S; i++ ){ if(covered_by[i] == 0) for(int d : sets[i]) hits_uncovered[d]++; }
    // for( int i=0; i<sets.size(); i++ ) assert(covered_by[i] > 0);
    // for( int i=0; i<sets.size(); i++ ){ if(covered_by[i] == 0) for(int d : sets[i]) hits_uncovered[d]++; } // #TEST
    auto cmp_nonhs = [&](const int a, const int b){
        if( isFrozen(a) && !isFrozen(b) ) return true;
        if( isFrozen(b) && !isFrozen(a) ) return false;

        if constexpr (use_timestamps) {
            if ( abs(timestamp[a] - iteration_counter ) > MAX_TIMESTAMP_DIFF ) return true;
            if ( abs(timestamp[b] - iteration_counter ) > MAX_TIMESTAMP_DIFF ) return false;
        }

        if (isRandomMoveCounterInValidInterval()) {
            // if( isFrozen(a) && !isFrozen(b) ) return true;
            // if( isFrozen(b) && !isFrozen(a) ) return false;

            // if(covers_alone[a] != covers_alone[b]) return covers_alone[a] < covers_alone[b];
            // if ( use_cc_for_nonhs_nodes ) if( conf_check[a] != conf_check[b] ) return cmp_cc(a,b); // #TEST
            return timestamp[a] > timestamp[b];
            // return timestamp[a] * visit_frequencies_rem[a] < timestamp[b] * visit_frequencies_add[b];
            // if constexpr(use_cc) if ( use_cc_for_nonhs_nodes ) if( conf_check[a] != conf_check[b] ) return cmp_cc(a,b);
            // return perm[a] < perm[b];
        }

        // if constexpr( use_cc && use_cc_for_nonhs_nodes ) if( conf_check[a] != conf_check[b] ) return cmp_cc(a,b);
        // if( hits_uncovered[a] != hits_uncovered[b] ) return hits_uncovered[a] > hits_uncovered[b];
        if( hits_uncovered[a] != hits_uncovered[b] ) return hits_uncovered[a] < hits_uncovered[b];
        if constexpr(use_cc) if ( use_cc_for_nonhs_nodes ) if( conf_check[a] != conf_check[b] ) return cmp_cc(a,b);
        if constexpr (use_timestamps) if ( abs(timestamp[a] - timestamp[b]) > EQUAL_TIMESTAMP_SPAN ) {
            return timestamp[a] > timestamp[b];
        }
        if constexpr (use_visit_frequencies) {
            // int vfa = visit_frequencies[a], vfb = visit_frequencies[b];
            int vfa = visit_frequencies_add[a], vfb = visit_frequencies_add[b];
            double r = 1.0 * vfa / vfb;
            if( r < 1.0/VISIT_FREQUENCIES_COEF || r > VISIT_FREQUENCIES_COEF ) {
                return vfa > vfb; // better node is the one that was changed less often
                // return vfa < vfb; // counterintuitively: select the node that was selected most often
            }
        }
        return perm[a] < perm[b];
    };
    VVI nonhs_nodes(S+1);
    int max_nonhs_index = 0;
    for( int i=0; i<N; i++ ) {
        nonhs_nodes[ hits_uncovered[i] ].push_back(i);
        max_nonhs_index = max(max_nonhs_index, hits_uncovered[i]);
    }
    auto addNonhsNode = [&](const int d) {
        nonhs_nodes[hits_uncovered[d]].push_back(d);
        max_nonhs_index = max(max_nonhs_index, hits_uncovered[d]);
    };

    auto correctMaxNonhsIndex = [&](int by = 50){
        int cnt = 0;
        if (max_nonhs_index < 0) max_nonhs_index = 0;
        for( int i=max_nonhs_index; i<(int)nonhs_nodes.size() && cnt++ < by; i++ ){
            if( i < nonhs_nodes.size() && !nonhs_nodes[i].empty() ) max_nonhs_index = i;
        }
    };


    auto getRandomHsnode = [&]() {
        assert(!hs_nodes.empty());
        int v = hs_nodes.heap[ 1 + rnd.nextInt(hs_nodes.size() ) ]->val;
        return v;
    };

    auto getRandomHsnodeBiased = [&]() {
        assert(!hs_nodes.empty());
        // int v = hs_nodes.heap[ 1 + (int)sqrt( rnd.nextInt(hs_nodes.size() * hs_nodes.size() ) ) ]->val;
        int v = hs_nodes.heap[ hs_nodes.size() - (int)sqrt( rnd.nextInt(hs_nodes.size() * hs_nodes.size() ) ) ]->val;
        return v;
    };

    //*************************************


    // constexpr bool use_soft_sets = true;
    // VI covers_alone_soft;
    // VI hits_uncovered_soft;
    // VI covered_by_soft;
    // VVI covered_by_nodes_soft;
    // int uncovered_soft = 0;
    // if constexpr (use_soft_sets) {
    //     covers_alone_soft = VI(N,0);
    //     hits_uncovered_soft = VI(N,0);
    //     covered_by_soft = VI(S,0);
    //     covered_by_nodes_soft = VVI(S);
    //
    //     for( int v : hs ) for( int d : V[v] ) {
    //         covered_by_soft[d]++;
    //         covered_by_nodes_soft[d].push_back(v);
    //     }
    //     for( int i=0; i<removed_sets.size(); i++ ) if( covered_by_soft[i] == 0 ) uncovered_soft++;
    //
    //     for( int i=0; i<removed_sets.size(); i++ ) {
    //         if(covered_by_soft[i] == 1) for( int d : removed_sets[i] ) if(in_hs[d]) covers_alone_soft[d]++;
    //     }
    //
    //     for( int i=0; i<removed_sets.size(); i++ ) {
    //         if(covered_by_soft[i] == 0) for(int d : removed_sets[i]) hits_uncovered_soft[d]++;
    //     }
    // }

    bool removed_sets_hit = false;
    auto setRemovedSetsHit = [&]() {
        removed_sets_hit = true;
        for( auto & zb : removed_sets ) {
            bool h = false;
            for(int d : zb) h |= in_hs[d];
            if(!h) { removed_sets_hit = false; break; }
        }
    };

    auto addBackNextSet = [&]() {
        if(removed_sets.empty()) return;
        // for( int i=0; i<min((int)removed_sets.size(), set_addition_frequency); i++ ) { // original
        for( int i=0; i<min((int)removed_sets.size(), set_addition_frequency); i++ ) {
        // int T = removed_sets.size();
        // int beg = rnd.nextInt(T), end = (beg+min((int)removed_sets.size()-1, set_addition_frequency))%T;
        // for( int i=beg; i != end; i = (i+1)%T ) {
            bool is_hit = false;
            for(int d : removed_sets[i]) is_hit |= in_hs[d];
            if(is_hit) {
                swap(removed_sets[i], removed_sets.back());
                break;
            }
        }

        auto zb = removed_sets.back();
        // clog << "\tAdding back new set, zb: " << zb << endl;
        // DEBUG(current_state_size);

        removed_sets.pop_back();
        sets.push_back( zb );
        const int id = sets.size()-1;
        assert(covered_by_nodes[id].empty());
        assert(covered_by[id] == 0);

        for( int d : zb ) V[d].push_back(id);

        int hit_by = 0;
        for(int d : zb) hit_by += in_hs[d];

        if(hit_by == 0) {
            uncovered++;
            for( int d : zb ) hits_uncovered[d]++;
            // int ind = rnd.nextInt(zb.size());
            // nodes_to_add_back.push_back( zb[ind] );

            int v = zb[0];
            for(int d : zb) if( cmp_nonhs(v,d) ) v = d;
            nodes_to_add_back.push_back( v );
            assert(!in_hs[v]);
            // clog << "\tadded set is not hit, adding node v: " << v << " to nodes_to_add_back" << endl;
        }
        if(hit_by == 1) {
            for(int d : zb) if(in_hs[d]) {
                // clog << "\tadded set is hit only by one node, d: " << d << ", updating hs_nodes" << endl;
                covers_alone[d]++;
                conf_check[d] = true;
                hs_nodes.set(d,d);
            }
        }
        covered_by[id] = hit_by;
        if(hit_by >= 1) for(int d : zb) if(in_hs[d]) covered_by_nodes[id].push_back(d);
    };
    //*************************************




    VI nodes_to_remove;
    int init_nodes_to_remove_size = 0;
    int last_node_added = -1;

    VI BMS; BMS.reserve(10);

    VB helper(N);

    auto getNodeToRemove = [&](){
        if (!nodes_to_remove.empty()) {
            auto v = nodes_to_remove.back();
            nodes_to_remove.pop_back();
            while(!in_hs[v] && !nodes_to_remove.empty()) {
                v = nodes_to_remove.back();
                nodes_to_remove.pop_back();
            }
            if(in_hs[v]) return v;
        }

        if constexpr (use_cc) if(use_cc_for_hs_nodes){
            if (use_hsn_que){
                int t = hsn_que.front();
                hsn_que.pop_front();
                in_hsn_que[t] = false;
                return t;
            }
            else return getRandomHsnode();
        }

        // // constexpr int FREQ = 1'000;
        // constexpr int FREQ = 100;
        // if(rnd.nextInt(FREQ) == 0) { // #TEST just a bit more randomization...
        //     assert(!hs_nodes.empty());
        //     // return getRandomHsnode();
        //     // return hs_nodes.heap[ 1 + rnd.nextInt(min(50,(int)sqrt(hs_nodes.size())) ) ]->val;
        //     // return hs_nodes.heap[ 1 + rnd.nextInt(min(50,max(1,(int)sqrt(hs_nodes.size()))) ) ]->val;
        //
        //     { // selection with nonuniform probability
        //         const int F = min(30, (int)pow(hs_nodes.size(), 0.66) );
        //         // int ind = rnd.nextInt(min(F,max(1,(int)sqrt(hs_nodes.size())))); // original
        //         // int ind = (int)sqrt(rnd.nextInt( F*F )); // larger indices are more probably
        //         int ind = F-1 - (int)sqrt(rnd.nextInt( F*F )); // smaller indices are more probable
        //         return hs_nodes.heap[ 1 + ind ]->val;
        //     }
        // }

        // // const bool use_bms = ((random_move_counter <= iters/4) && (rnd.nextInt(20) == 0));
        // // const bool use_bms = ((random_move_counter <= iters/4) && (random_move_counter % 20 == 0));
        // const bool use_random_move = (isRandomMoveCounterInValidInterval() && (rnd.nextInt(10) == 0)) && (uncovered == 0);
        // const int MAX_BMS_SIZE = 10;
        //
        // // if(use_random_move) return getRandomHsnode();
        //
        // if(true)
        // if (use_random_move) {
        //     // { // select a node that is a neighbor of a nonhs node in nonhs_nodes[max_nonhs_index]
        //     //     BMS.clear();
        //     //     for( int d : nonhs_nodes[max_nonhs_index] ) for( int dd : cc_mark_neighborhoods[d] ) {
        //     //         if(!helper[dd] && in_hs[dd]) {
        //     //             helper[dd] = true;
        //     //             BMS.push_back(dd);
        //     //         }
        //     //     }
        //     //     for(int d : BMS) helper[d] = false;
        //     //     if ( !BMS.empty() ) return BMS[ rnd.nextInt(BMS.size()) ];
        //     // }
        //
        //     BMS.clear();
        //     int cnt = 0;
        //     for( auto item : hs_nodes.heap ) if(item != nullptr){
        //         int u = item->val;
        //         if( !isForbiddenState( current_state_hash ^ hashes[u] ) ) {
        //             // if ( BMS.empty() || covers_alone[u] <= 1 + covers_alone[BMS[0]] ) {
        //             // if ( BMS.empty() || covers_alone[u] == covers_alone[BMS[0]] ) {
        //             // if( hits_uncovered[u] > 0 )
        //             {
        //                 BMS.push_back(u);
        //                 if (BMS.size() > MAX_BMS_SIZE) break;
        //             }
        //         }
        //         if(cnt++ >= 3*MAX_BMS_SIZE) break;
        //     }
        //
        //     // while( !BMS.empty() && covers_alone[BMS.back()] != covers_alone[BMS[0]] ) BMS.pop_back();
        //     if ( !BMS.empty() ) return BMS[ rnd.nextInt(BMS.size()) ];
        //     // if(!BMS.empty()){
        //     //     int v = BMS[0];
        //     //     for(int d : BMS) {
        //     //         // if(perm[d] > perm[v]) v = d;
        //     //         if(perm[d] < perm[v]) v = d;
        //     //         // if( covers_alone[d] > covers_alone[v] ) v = d;
        //     //         // if( hits_uncovered[d] < hits_uncovered[v] ) v = d;
        //     //         // if( timestamp[d] < timestamp[v] ) v = d;
        //     //         // if( visit_frequencies_add[d] + visit_frequencies_rem[d] < visit_frequencies_add[v] + visit_frequencies_rem[v] ) v = d;
        //     //     }
        //     //     return v;
        //     // }
        // }


        // constexpr int FREQ = 50;
        // if(isRandomMoveCounterInValidInterval())
        // if(rnd.nextInt(FREQ) == 0) return getRandomHsnode();
        // if(rnd.nextInt(FREQ) == 0) return getRandomHsnodeBiased();

        {
            int u = getRandomHsnode();
            if constexpr (use_timestamps) if ( abs(timestamp[u] - iteration_counter ) > MAX_TIMESTAMP_DIFF )
                return u;
        }

        {
            const bool use_frozen = (rnd.nextInt(10) == 0);
            int best_v = -1, cnt = 0;
            for( auto item : hs_nodes.heap ){
                if(item != nullptr) {
                // if( (item != nullptr) && (item->val != last_node_added) ) {
                    int u = item->val;
                    if (covers_alone[u] == 0) return u;

                    if( isForbiddenState( current_state_hash ^ hashes[u] ) ) continue;
                    // if (isRandomMoveCounterInValidInterval()) {
                        if( use_frozen && isFrozen(u) && !( covers_alone[u] == uncovered ) ) continue; // #TEST
                        if( !conf_check[u] ) continue; // #TEST
                        if(u == last_node_added) continue; // #TEST
                    // }
                    // return u;

                    // if constexpr (use_timestamps) if ( abs(timestamp[u] - iteration_counter ) > MAX_TIMESTAMP_DIFF )
                    //     return u;

                    if(best_v != -1) cnt++;
                    if(cnt >= 6) return best_v;
                    if( best_v == -1 || cmp_hs(u, best_v) ) best_v = u;
                    // if( best_v == -1 || cmp_hs(u, best_v) || rnd.nextInt(100) == 0 ) best_v = u;
                }
            }
            if(best_v != -1) return best_v;
        }

        return getRandomHsnode();

        // int v = -1;
        // int cnt = 0;
        // const int THR = (N<<6);
        // do{
        //     v = rnd.nextInt(N);
        // }while( !in_hs[v] && cnt++ < THR );
        //
        // return (in_hs[v] ? v : -1 );
    };


    VI counters(N,0);

    auto isNonhsNodeDominatedByOtherNonhsNode = [&](int v) {
        assert(!in_hs[v]);

        for( int d : V[v] ) if( covered_by[d] == 0 ) for( int dd : sets[d] ) counters[dd] += (dd != v && !in_hs[dd]);

        int dominator = -1;
        for( int d : V[v] ) if( covered_by[d] == 0 ) {
            for( int dd : sets[d] ) if(dd != v && !in_hs[dd]) {
                assert(counters[dd] <= hits_uncovered[v]);
                // if ( counters[dd] == hits_uncovered[v] ) {
                if ( counters[dd] == hits_uncovered[v]
                    // && (hits_uncovered[dd] > hits_uncovered[v] || (hits_uncovered[dd] == hits_uncovered[v] && perm[dd] < perm[v]) )
                    && timestamp[dd] < timestamp[v]
                    ) {
                    dominator = dd;
                    break;
                }
            }
            break;
        }

        for( int d : V[v] ) if( covered_by[d] == 0 ) for( int dd : sets[d] ) counters[dd] = 0;

        return dominator != -1;
    };

    int last_node_removed = -1;

    VB was_add(N);

    // greedily select the best node to add to current hs - the one that will cover greatest number of uncovered sets
    auto getNodeToAdd = [&](){
        // if constexpr (use_dynamic_sets) if( !nodes_to_add_back.empty() ) {
        // if (use_dynamic_sets)
        if( !nodes_to_add_back.empty() ) {
            int v = nodes_to_add_back.front();
            nodes_to_add_back.pop_front();
            while(in_hs[v] && !nodes_to_add_back.empty()) {
                v = nodes_to_add_back.front();
                nodes_to_add_back.pop_front();
            }
            // assert(!in_hs[v]);
            // clog << "\tReturning node from nodes_to_add_back" << endl;
            if(!in_hs[v]) return v;
        }


        // const bool add_random = ((random_move_counter <= iters/2) ? true : ( rnd.nextInt(5) == 0 ) );
        // const bool add_random = ((random_move_counter <= iters/2) ? (rnd.nextInt(4) > 0) : ( rnd.nextInt(8) == 0 ) );
        // const bool add_random = ((random_move_counter <= iters/2) ? (rnd.nextInt(3) > 0) : ( rnd.nextInt(5) == 0 ) );
        // const bool add_random = (isRandomMoveCounterInValidInterval() ? (rnd.nextInt(3) > 0) : ( rnd.nextInt(10) == 0 ) );
        const bool add_random = (isRandomMoveCounterInValidInterval() ? (rnd.nextInt(3) > 0) : ( rnd.nextInt(50) == 0 ) );
        // const bool add_random = ((random_move_counter <= iters/2) ? (rnd.nextInt(2) == 0) : ( rnd.nextInt(10) == 0 ) );
        // const bool add_random = (rnd.nextInt(3) > 0);
        // const bool add_random = (rnd.nextInt(3) == 0);
        // const bool add_random = (rnd.nextInt(5) == 0);
        // const bool add_random = (rnd.nextInt(10) == 0);
        // const bool add_random = (rnd.nextInt(20) == 0);
        // constexpr bool add_random = false;
        // if (add_random && !allow_to_add_back_only_uncovered_cost_nodes) {
        if (add_random) {
            // if((random_move_counter % 250) > 0) {
            if(true) {
                int init_mni = max_nonhs_index;
                bool retain_init_mni = false;

                // if( (rnd.nextInt(10) == 0) && !allow_to_add_back_only_uncovered_cost_nodes ) {
                //     retain_init_mni = true;
                //     if(max_nonhs_index > 0 ) max_nonhs_index--;
                //     // if(max_nonhs_index > 0 && max_nonhs_index < uncovered ) max_nonhs_index--;
                // }

                while (max_nonhs_index >= 0) {
                    REMCVAL(in_hs,nonhs_nodes[max_nonhs_index]);
                    if(allow_to_add_back_only_uncovered_cost_nodes) { // removing all nodes
                        auto fun = [&](int ind){ int v = nonhs_nodes[max_nonhs_index][ind]; return hits_uncovered[v] != max_nonhs_index; };
                        REMCFUN(fun,nonhs_nodes[max_nonhs_index]);
                        for(int d : nonhs_nodes[max_nonhs_index]) assert( hits_uncovered[d] == max_nonhs_index );
                    }

                    // { // making unique
                    //     auto & vec = nonhs_nodes[max_nonhs_index];
                    //     for( int i=(int)vec.size()-1; i>=0; i-- ) {
                    //         if(was_add[vec[i]]){ REM(vec,i); }
                    //         else was_add[vec[i]] = true;
                    //     }
                    //     for(int d : vec) was_add[d] = false;
                    // }

                    if ( nonhs_nodes[max_nonhs_index].empty() ) {
                        max_nonhs_index--;
                    }
                    else {
                        int ind = max_nonhs_index;
                        if(retain_init_mni) {
                            max_nonhs_index = init_mni;
                            while(max_nonhs_index > 0 && nonhs_nodes[max_nonhs_index].empty()) max_nonhs_index--;
                        }
                        return nonhs_nodes[ind][ rnd.nextInt( nonhs_nodes[ind].size() ) ];
                    }
                }
                if(retain_init_mni) {
                    max_nonhs_index = init_mni;
                    while(max_nonhs_index > 0 && nonhs_nodes[max_nonhs_index].empty()) max_nonhs_index--;
                }
            }else if(!allow_to_add_back_only_uncovered_cost_nodes) {
                int v = -1;
                int t = 1;
                while(t <= max_nonhs_index) {
                    REMCVAL(in_hs,nonhs_nodes[t]);
                    if( nonhs_nodes[t].empty() ) t++;
                    else {
                        int p = rnd.nextInt( nonhs_nodes[t].size() );
                        v = nonhs_nodes[t][p];
                        break;
                    }
                }

                while( nonhs_nodes[max_nonhs_index].empty() ) max_nonhs_index--;

                if(v != -1) return v;
                else {
                    assert(!nonhs_nodes[max_nonhs_index].empty());
                    int p = rnd.nextInt( nonhs_nodes[max_nonhs_index].size() );
                    return nonhs_nodes[max_nonhs_index][p];
                }
            }

        }

        int bestv = -1;
        int any_v = -1;

        bool retain_max_nonhs_index = false;
        int init_max_nonhs_index = max_nonhs_index;
        {
            while( max_nonhs_index >= 0 ) {
                auto & vec = nonhs_nodes[max_nonhs_index];
                for(int i=(int)vec.size()-1; i>=0; i--) {
                    int v = vec[i];
                    if( in_hs[v] || hits_uncovered[v] != max_nonhs_index ) { // original
                        swap(vec[i], vec.back());
                        vec.pop_back();
                    }else {
                        if( any_v == -1 ) any_v = v;

                        if( (bestv == -1 || cmp_nonhs( bestv, v ))
                             && (!use_tabu_for_nonhs || !isForbiddenState( current_state_hash ^ hashes[v] ))
                             ){
                            // if( v != last_node_removed ) // #TEST
                                // if (!isNonhsNodeDominatedByOtherNonhsNode(v)) // #TEST
                                bestv = v; // original
                                // if( !isFrozen(v) ) bestv = v;
                                // else retain_max_nonhs_index = true;
                             }
                    }
                }
                if( allow_to_add_back_only_uncovered_cost_nodes && any_v != -1 ){
                    return (bestv == -1) ? any_v : bestv;
                }
                if( bestv == -1 ) {
                    if( use_tabu_for_nonhs && !nonhs_nodes[max_nonhs_index].empty() ) retain_max_nonhs_index = true;
                    max_nonhs_index--;
                    if(!retain_max_nonhs_index) init_max_nonhs_index--;
                }
                else {
                    if( retain_max_nonhs_index ) max_nonhs_index = init_max_nonhs_index;
                    return bestv;
                }
            }
        }

        if( retain_max_nonhs_index ) max_nonhs_index = init_max_nonhs_index;

        return any_v;
    };

    VB was(N,false);
    VB was2(N,false);


    constexpr bool use_continuous_perm_deviation = true;
    // const int deviate_perm_frequency = max(500, (int)pow(N,0.85)); // original
    constexpr int deviate_perm_frequency = inf; // #TEST

    constexpr int PREM_DEV_REPS = 0;



    auto considerNodeDomination = [&](int v) {
        assert(in_hs[v]);
        if( covers_alone[v] == 0 ) return false;

        for( int d : V[v] ) if( covered_by[d] == 1 ) for( int dd : sets[d] ) counters[dd] += (dd != v && !in_hs[dd]);

        int dominator = -1;
        for( int d : V[v] ) if( covered_by[d] == 1 ) {
            for( int dd : sets[d] ) if(dd != v) {
                // bool cond = (counters[dd] + hits_uncovered[dd] >= covers_alone[v]);

                bool cond = (counters[dd] + hits_uncovered[dd] > covers_alone[v]);
                if (counters[dd] + hits_uncovered[dd] == covers_alone[v] ) {
                    if (dominator == -1) cond |= ( timestamp[dd] < timestamp[v] );
                    else cond |= ( timestamp[dd] < timestamp[dominator] );
                }

                cond &= (!isForbiddenState( current_state_hash ^ hashes[v] ^ hashes[dd]));

                if( cond ) {
                    dominator = dd;
                    shuffle(sets[d],rnd);
                    break;
                }
            }
            break;
        }

        for( int d : V[v] ) if( covered_by[d] == 1 ) for( int dd : sets[d] ) counters[dd] = 0;

        if( dominator != -1 ) {
            // {
            //     clog << "Found dominator!!" << endl << "v: " << v << ", covers_alone: " << covers_alone[v] << endl;
            //     clog << "dominator: " << dominator << ", hits_uncovered: " << hits_uncovered[dominator] << endl;
            //     assert(!in_hs[dominator]);
            //     exit(2);
            // }

            nodes_to_remove.push_back(v);
            nodes_to_add_back.push_back(dominator);
            return true;
        }

        return false;
    };

    VB set_always_hit(S,true);
    VB nodes_touched(N);
    VB nodes_touched_with_neigh(N);

    VI temp;

    auto reorderPermForBFS = [&](VI & perm, int v) {
        was[v] = true;
        VB was2(S);
        VI temp2;
        temp.clear();
        for( int d : V[v] ) for( int u : sets[d] ) {
            if(!was[u]) {
                temp.push_back(u);
                was[u] = true;
            }
        }
        if(rnd.nextInt(2))
            stable_partition(ALL(perm), [&]( int a ){ return was[a]; });
        // temp = {v}; // uncomment to use only first neighborhood
        for( int vv : temp ) for( int d : V[vv] ) if( !was2[d] ){ was2[d] = true; temp2.push_back(d); }
        for( int d : temp2 ) for( int u : sets[d] ) was[u] = true; // secondary neighborhood
        stable_partition(ALL(perm), [&]( int a ){ return was[a]; });
        temp.clear();
        fill(ALL(was),false);
    };


    {
        // StandardUtils::shuffle(perm);
        shuffle(perm,rnd);
        reorderPermForBFS(perm, rnd.nextInt(N));
        // reorderPermForBFS2(perm, rnd.nextInt(N));
        for( int i=0; i<N; i++ ) hs_nodes.set(i,i);
        for (int i = 0; i < N; i++) if (!in_hs[i]) hs_nodes.removeFromHeap(i);
    }




    const double avg_elements_per_set = accumulate(ALL(sets), 0.0,
        [](double s, auto & v){return s + v.size();}) / sets.size();
    if constexpr (enable_logs) DEBUG(avg_elements_per_set);


    const bool search_below_threshold = (hs.size() >= 5 && (avg_elements_per_set <= N/50 || N <= 1'000)
        // && (rnd.nextInt(3) == 0) ); // original
        // && (rnd.nextInt(7) == 0) && (S != N) );
        && (rnd.nextInt(11) == 0) && (S != N) );
    bool is_below_threshold = false;
    const int min_iter_for_search_below_threashold = 0; // set to 0 to start at the first iteration
    const int max_iter_for_search_below_threashold = iters / 2; // original

    if constexpr (enable_logs) DEBUG(search_below_threshold);
    if constexpr (enable_logs) DEBUG(use_tabu_for_nonhs);

    const int cc_clear_frequency = 1 + (iters / 7); // 5 seems to work ok
    int cc_clear_index = 0;

    for( int itr = 0; itr < iters; itr++ ) {
        // if(itr % 1000 == 0) clog << "\ritr #" << itr <<  ", current_state_size: " << current_state_size <<
        //     ", allow_to_add_back_only_uncovered_cost_nodes: " << allow_to_add_back_only_uncovered_cost_nodes
        //     << "\t\t" << flush; // uncomment this to enable logging process

        iteration_counter++;
        if((itr % NODE_FREEZE_TIME_CHANGE_FREQUENCY) == 0) NODE_FREEZE_TIME += NODE_FREEZE_CHANGE_STEP;

        if(iteration_counter == MAX_RANDOM_MOVE_COUNTER_VALUE + 2) {
            for(int i=0; i<N; i++) hs_nodes.removeFromHeap(i);
            for(int i=0; i<N; i++) hs_nodes.set(i,i);
            for(int i=0; i<N; i++) if(!in_hs[i]) hs_nodes.removeFromHeap(i);
        }

        // if (!isRandomMoveCounterInValidInterval())
         if(!allow_to_add_back_only_uncovered_cost_nodes && nodes_to_remove.empty() && nodes_to_add_back.empty()) {
             if (rnd.nextInt(3) == 0) {
                int v = getRandomHsnode();
                considerNodeDomination(v);
             }
         }

        // if( itr % cc_clear_frequency == 0 ) {
        if( ++cc_clear_index == cc_clear_frequency ) {
            cc_clear_index = 0;
            // for(int i=0; i<N; i++) if( !in_hs[i] ) conf_check[i] = false;
            for(int i=0; i<N; i++) if( !in_hs[i] ) {
                // conf_check[i] = false;
                // if( conf_check[i] ) conf_check[i] = (rnd.nextInt(7) == 0);
                // if( conf_check[i] ) conf_check[i] = (rnd.nextInt(16) == 0);
                // if( conf_check[i] ) conf_check[i] = !(rnd.nextInt(16) == 0);
                // if( conf_check[i] ) conf_check[i] = rnd.nextInt(2);
                if( conf_check[i] ) conf_check[i] = true;
            }
        }

        // if( (itr & 127) == 0 ) if( sw.tle() ) break;
        if( (itr & 511) == 0 ) if( sw.tle() ) break;

        removeOldForbiddenStates();

        if constexpr(use_continuous_perm_deviation) {

            for(int reps=0; reps<PREM_DEV_REPS; reps++){
                int a,b;
                if( (itr >> 7) & 3 ) {
                    a = rnd.nextInt(N);
                    b = rnd.nextInt(N);
                }else {
                    a = hs_nodes.heap[ 1 + rnd.nextInt(hs_nodes.heap.size()-1 )]->val;
                    b = hs_nodes.heap[ 1 + rnd.nextInt(hs_nodes.heap.size()-1 )]->val;
                }

                while(b == a) b = rnd.nextInt(N);

                if(in_hs[a]) hs_nodes.removeFromHeap(a);
                if(in_hs[b]) hs_nodes.removeFromHeap(b);

                swap(perm[a], perm[b]);

                if(in_hs[a]) hs_nodes.set(a,a);
                if(in_hs[b]) hs_nodes.set(b,b);
            }
        }


        // if (itr % deviate_perm_frequency == 0) {
        //     StandardUtils::shuffle(perm);
        //     if(max_nonhs_index >= 0) {
        //         int ind = rnd.nextInt(nonhs_nodes[max_nonhs_index].size());
        //         reorderPermForBFS(perm, nonhs_nodes[max_nonhs_index][ind]);
        //     }
        //     for( int i=0; i<N; i++ ) hs_nodes.set(i,i);
        //     for (int i = 0; i < N; i++) if (!in_hs[i]) hs_nodes.removeFromHeap(i);
        //     for( auto & v : nonhs_nodes ) v.clear();
        //     for( int i=0; i<N; i++ ) if(!in_hs[i]) addNonhsNode(i); // original
        // }

        // const int FACTOR = ( (N <= 1e4) ? 1 : ( (N <= 1e5) ? 7 : 25 ) );
        // const int FREQ = 200 * FACTOR;
        // if( (itr % FREQ ) == 0 ) {
        //
        //     max_nonhs_index = max(max_nonhs_index, 0);
        //     for( int i=max_nonhs_index; i<=max_nonhs_index; i++ ) {
        //     // for( int i=max(0,max_nonhs_index-3); i<=max_nonhs_index; i++ ) {
        //         auto & vec = nonhs_nodes[i];
        //         for( int j=(int)vec.size()-1; j>=0; j-- ) {
        //             int v = vec[j];
        //             if( was[v] || in_hs[v] ) REM(vec,j);
        //             was[v] = true;
        //         }
        //         for(int v : vec) was[v] = false;
        //     }
        // }



        int k_swaps = 1;
        if(itr < min_iter_for_search_below_threashold || itr > max_iter_for_search_below_threashold) {
            is_below_threshold = true; //  using this, we can use below threshold only in first/second part of iterations
        }
        if( search_below_threshold && !is_below_threshold && current_state_size >= 5 && uncovered == 0 ) {
            k_swaps = 2;
            is_below_threshold = true;
        }

        const int MAX_NODES_TO_REMOVE_SIZE = min(50.0 , 10 + 0.1 * hs.size() );
        // const int avg_V_deg = avg_elements_per_set * S / N;
        // const int MAX_NODES_TO_REMOVE_SIZE = max(15, avg_V_deg );
        bool use_neighborhood_removal = false;
        // bool init_to_remove_with_random_hs_node = false;
        if (admit_neighborhood_removal && !search_below_threshold && !use_dynamic_sets
            && current_state_size > 2*MAX_NODES_TO_REMOVE_SIZE && !allow_to_add_back_only_uncovered_cost_nodes) {
            // const int FREQ = 10 * MAX_NODES_TO_REMOVE_SIZE; // 10 seems to be a very good value
            const int FREQ = ( (itr <= iters/2) ? 14 : 7 ) * MAX_NODES_TO_REMOVE_SIZE; // 10 seems to be a very good value
            if ( rnd.nextInt(FREQ) == 0 && (itr + 100*FREQ < iters) ) {
            // if ( (itr % FREQ == 0) && (itr + 10*FREQ < iters) && nodes_to_remove.empty() ) {
                use_neighborhood_removal = true;

                nodes_to_add_back.clear(); nodes_to_remove.clear(); // #TEST
                assert(nodes_to_remove.empty());
            }
        }


        for( int swp_iter = 0; swp_iter < k_swaps; swp_iter++ ) {
            //******************************//****************************** removing node
            if( hs_nodes.empty() ) break;
            if( use_tabu_for_nonhs ) correctMaxNonhsIndex();

            { // remove node from current hs
                int v = getNodeToRemove();
                if(v == -1) break;
                if( v == last_node_added ) {
                    if (!use_cc || !use_cc_for_hs_nodes || !use_hsn_que) {
                        int max_best_cnt = ( (last_valid_state_size <= 100) ? hs_nodes.size() :
                            // pow( hs_nodes.size(), 0.5 ) );
                            log( hs_nodes.size() ) );
                        v = hs_nodes.heap[ 1 + rnd.nextInt(max_best_cnt) ]->val;
                    }
                }


                if (use_neighborhood_removal && swp_iter == 0) {
                    if( uncovered == 0 ) v = getRandomHsnode();

                    if ( !cc_mark_neighborhoods[v].empty() ) {
                        int ind = rnd.nextInt( cc_mark_neighborhoods[v].size() );
                        const int T = cc_mark_neighborhoods[v].size();
                        for ( int i=(ind+1)%T; i != ind; i = (i+1) % T ) {
                            int d = cc_mark_neighborhoods[v][i];
                            if (d != v && in_hs[d]) nodes_to_remove.push_back(d);
                        }
                    }else {
                        for ( int d : V[v] ) {
                            for ( int dd : sets[d] ) if ( dd != v && in_hs[dd] ) nodes_to_remove.push_back(dd);
                            StandardUtils::makeUnique(nodes_to_remove);
                        }
                    }

                    // { // now add another neighborhood... ?? it does not seem to give any additional edge...
                    //     auto temp = nodes_to_remove;
                    //     for ( int d : nodes_to_remove ) was[d] = true;
                    //     for (int d : temp) for (int dd : cc_mark_neighborhoods[d]) if (dd != v && !was[dd] && in_hs[dd]) {
                    //         was[dd] = true;
                    //         nodes_to_remove.push_back(dd);
                    //     }
                    //     for ( int d : nodes_to_remove ) was[d] = false;
                    // }

                    // { // now add another neighborhood... ?? it does not seem to give any additional edge...
                    //     // while( nodes_to_remove.size() < MAX_NODES_TO_REMOVE_SIZE ) {
                    //         auto temp = nodes_to_remove;
                    //         for ( int d : temp ) was[d] = was2[d] = true;
                    //         for( int i=0; i<temp.size(); i++ ) {
                    //             int u = temp[i];
                    //             for( int d : V[u] ) for(int dd : sets[d]) if( !was2[dd] ) {
                    //                 was2[dd] = true;
                    //                 temp.push_back(dd);
                    //                 if(in_hs[dd] && dd != v) nodes_to_remove.push_back(dd);
                    //                 if(nodes_to_remove.size() >= MAX_NODES_TO_REMOVE_SIZE) break;
                    //             }
                    //             if(nodes_to_remove.size() >= MAX_NODES_TO_REMOVE_SIZE) break;
                    //         }
                    //
                    //         for ( int d : temp ) was[d] = was2[d] = false;
                    //     // }
                    // }

                    if (nodes_to_remove.size() > MAX_NODES_TO_REMOVE_SIZE) nodes_to_remove.resize(MAX_NODES_TO_REMOVE_SIZE);

                    if (nodes_to_remove.size() > MAX_NODES_TO_REMOVE_SIZE) {
                        int opt = rnd.nextInt(3);
                        // int opt = 2;

                        if( opt == 0 ) {
                            // sort(ALL(nodes_to_remove), cmp_hs);
                            nth_element(nodes_to_remove.begin(), nodes_to_remove.begin() + MAX_NODES_TO_REMOVE_SIZE, nodes_to_remove.end(), cmp_hs);
                        }else if(opt == 1) {
                            nth_element(nodes_to_remove.begin(), nodes_to_remove.begin() + MAX_NODES_TO_REMOVE_SIZE, nodes_to_remove.end(),
                            // [&](int a, int b){ return visit_frequencies_rem[a] < visit_frequencies_rem[b];} );
                            [&](int a, int b){ return visit_frequencies_rem[a] > visit_frequencies_rem[b];} );
                        }else {
                            shuffle(nodes_to_remove, rnd);
                        }

                            // if(rnd.nextInt(4) == 0) reverse(ALL(nodes_to_remove));
                        nodes_to_remove.resize(MAX_NODES_TO_REMOVE_SIZE);
                    }

                    for(int d : nodes_to_remove) assert(d != v);

                    if (nodes_to_remove.empty() || (nodes_to_remove.size() > current_state_size / 2)) {
                        nodes_to_remove.clear();
                        use_neighborhood_removal = false;
                        k_swaps = 1;
                    }else {
                        // DEBUG(nodes_to_remove.size());
                        k_swaps = 1 + nodes_to_remove.size();
                        init_nodes_to_remove_size = nodes_to_remove.size();
                        // if (init_to_remove_with_random_hs_node) k_swaps = 1 + nodes_to_remove.size();
                        // else k_swaps = 1 + nodes_to_remove.size();
                    }
                }


                last_node_removed = v;
                last_node_added = -1;

                assert(in_hs[v]);
                current_state_hash ^= hashes[v];
                if constexpr (use_visited_states) markVisitedState(current_state_hash);
                current_state_size--;

                hs_nodes.removeFromHeap(v); // need to do that before reducing [covered_by]
                covers_alone[v] = 0;
                if constexpr (use_timestamps) timestamp[v] = itr;


                {
                    int a = rnd.nextInt(N);
                    if(a != v){
                        swap(perm[a], perm[v]);
                        if(in_hs[a]) hs_nodes.set(a,a);
                    }
                }

                in_hs[v] = false;
                for( int d : V[v] ){
                    covered_by[d]--;
                    total_cbn_iters++;
                    total_cbn_remove_size += covered_by_nodes[d].size();
                    // covered_by_nodes[d].erase(v);
                    auto fun = [&](int ind){ return covered_by_nodes[d][ind] == v; };
                    REMCFUN( fun, covered_by_nodes[d] );
                    if(covered_by[d] == 0) uncovered++;
                }


                { // updating hs_nodes other than v (v was updated earlier)
                    temp.clear();
                    for (int d : V[v]) {
                        if (covered_by[d] == 1) {
                            int u = *covered_by_nodes[d].begin();
                            if( !in_hs[u] ) continue;
                            if(!was[u]) {
                                was[u] = true;
                                temp.push_back(u);
                                if constexpr(!use_hsn_updates_instead_of_rem_add) hs_nodes.removeFromHeap(u);
                                // if (!use_hsn_updates_instead_of_rem_add) hs_nodes.removeFromHeap(u);
                            }
                            if constexpr(!use_hsn_updates_instead_of_rem_add) covers_alone[u]++;
                            // if (!use_hsn_updates_instead_of_rem_add) covers_alone[u]++;
                            else covers_alone_diff[u]++;
                        }
                    }

                    for(int d : temp) {
                        was[d] = false;
                        if constexpr(!use_hsn_updates_instead_of_rem_add) hs_nodes.set(d,d);
                        // if (!use_hsn_updates_instead_of_rem_add) hs_nodes.set(d,d);
                        else {
                            covers_alone[d] += covers_alone_diff[d];
                            covers_alone_diff[d] = 0;
                            hs_nodes.updateElement(d);
                        }
                    }
                    temp.clear();
                }

                { // updating nonhs_nodes
                    temp.clear();
                    for(int d : V[v]){
                        if(covered_by[d] == 0) {
                            for (int u : sets[d]) {
                                if(!was[u]) {
                                    was[u] = true;
                                    temp.push_back(u);
                                }
                                hits_uncovered[u]++;
                            }
                        }
                    }

                    for(int d : temp) {
                        was[d] = false;
                        addNonhsNode(d);
                    }
                    temp.clear();
                }

                // if(allow_to_add_back_only_uncovered_cost_nodes) // #TEST
                if(allow_to_add_back_only_uncovered_cost_nodes || (itr % 3 == 0) ) // #TEST
                    addNonhsNode(v);

                addStateChangeToHistory(v);

                if (!isRandomMoveCounterInValidInterval())
                    for( int d : neigh_via_deg2_sets[v] ) if( !in_hs[d] ) {
                        if(!allow_to_add_back_only_uncovered_cost_nodes || hits_uncovered[d] == uncovered)
                            if (!isForbiddenState( current_state_hash ^ hashes[d] ))
                            nodes_to_add_back.push_back(d);
                    }

                // frozen[v] = true;
                // frozen[v] = rnd.nextInt(2);
                frozen[v] = (rnd.nextInt(101) <= NODE_FREEZE_PROBAB);

                for (int d : V[v]) if ( covered_by[d] == 0 ) set_always_hit[d] = false;
                nodes_touched[v] = true;
                nodes_touched_with_neigh[v] = true;
                for (int d : cc_mark_neighborhoods[v]) nodes_touched_with_neigh[d] = true;


                if(uncovered == 0) setRemovedSetsHit();
                if(uncovered == 0 && removed_sets_hit) valid_state_change_history_marker.back() = true;

                // if constexpr (use_visit_frequencies) visit_frequencies[v]++;
                if constexpr (use_visit_frequencies) visit_frequencies_rem[v]++;
                // if constexpr (use_visit_frequencies) visit_frequencies_rem[v] = visit_frequencies_counter++;

                if constexpr(use_cc) if ( use_cc_for_hs_nodes || use_cc_for_nonhs_nodes ) mark_cc(v);
                // if constexpr(use_cc) if ( use_cc_for_hs_nodes || use_cc_for_nonhs_nodes ) conf_check[v] = true;
                if(last_node_added != -1) conf_check[last_node_added] = false;
            }
        } // for

        //******************************//****************************** adding node back

        // if constexpr (use_dynamic_sets) {
        if (use_dynamic_sets) {
            if( ++set_addition_iter == set_addition_frequency && !removed_sets.empty() ) {
                set_addition_iter = 0;
                addBackNextSet();
                // k_swaps += nodes_to_add_back.size();
            }

            removed_sets_hit = false;
            // const int FR = removed_sets.size() / 5 + 1;
            // if( (uncovered == 0) && ((itr % FR) == 0) ) setRemovedSetsHit();
            // if( uncovered == 0 && !removed_sets.empty() ) setRemovedSetsHit();
        }
        if(removed_sets.empty()) removed_sets_hit = true;

        if (!use_neighborhood_removal) k_swaps = 1;

        // assert(nodes_to_remove.empty());

        // k_swaps += nodes_to_add_back.size();
        if(use_dynamic_sets)
            k_swaps += nodes_to_add_back.size();
        // k_swaps += nodes_to_add_back.size(); // #TEST

        // if(use_neighborhood_removal) DEBUG(k_swaps);
        if(use_neighborhood_removal && !use_dynamic_sets) {
            // DEBUG(init_nodes_to_remove_size);
            // DEBUG(k_swaps);
            assert(k_swaps == init_nodes_to_remove_size + 1);
        }


        for( int swp_iter = 0; swp_iter < k_swaps; swp_iter++ ) {
            bool add_back = (uncovered > 0 );

            if(!add_back) nodes_to_add_back.clear();

            if(add_back){ // add node to current hs
                if( use_tabu_for_nonhs ) correctMaxNonhsIndex();

                int v = getNodeToAdd();
                if( v == -1 ) break;
                if( v == last_node_removed ) {
                    if ( max_nonhs_index < 0 || nonhs_nodes[max_nonhs_index].empty() ) correctMaxNonhsIndex();
                    assert(!nonhs_nodes[max_nonhs_index].empty());
                    int ind = rnd.nextInt( nonhs_nodes[max_nonhs_index].size() );
                    v = nonhs_nodes[max_nonhs_index][ind];
                    while(in_hs[v]) v = getNodeToAdd();
                }
                last_node_removed = -1;
                last_node_added = v;
                if constexpr (use_timestamps) timestamp[v] = itr;
                {
                    int a = rnd.nextInt(N);
                    swap(perm[a], perm[v]);
                    if(in_hs[a]) hs_nodes.set(a,a);
                }

                assert(!in_hs[v]);
                current_state_hash ^= hashes[v];
                if constexpr (use_visited_states) markVisitedState(current_state_hash);

                current_state_size++;

                { // update hs_nodes
                    temp.clear();
                    for (int d : V[v]) {
                        if (covered_by[d] == 1) {
                            int u = *covered_by_nodes[d].begin();
                            if( !in_hs[u] ) continue;

                            if(!was[u]) {
                                was[u] = true;
                                temp.push_back(u);
                                if constexpr(!use_hsn_updates_instead_of_rem_add) hs_nodes.removeFromHeap(u);
                                // if (!use_hsn_updates_instead_of_rem_add) hs_nodes.removeFromHeap(u);
                            }

                            if constexpr(!use_hsn_updates_instead_of_rem_add) covers_alone[u]--;
                            // if (!use_hsn_updates_instead_of_rem_add) covers_alone[u]--;
                            else covers_alone_diff[u]--;
                        }else if( covered_by[d] == 0 ){
                            covers_alone[v]++;
                        }
                    }

                    for(int d : temp) {
                        was[d] = false;
                        if constexpr(!use_hsn_updates_instead_of_rem_add) hs_nodes.set(d,d);
                        // if (!use_hsn_updates_instead_of_rem_add) hs_nodes.set(d,d);
                        else {
                            covers_alone[d] += covers_alone_diff[d];
                            covers_alone_diff[d] = 0;
                            hs_nodes.updateElement(d);
                        }
                    }
                    temp.clear();

                    // if constexpr (use_visit_frequencies) visit_frequencies[v]++;
                    if constexpr (use_visit_frequencies) visit_frequencies_add[v]++;
                    // if constexpr (use_visit_frequencies) visit_frequencies_add[v] = visit_frequencies_counter++;

                    hs_nodes.set(v,v);
                    addStateChangeToHistory(v);
                    // if (use_hsn_que)
                    if (use_hsn_que && !in_hsn_que[v])
                        hsn_que.push_back(v);
                }

                {// udate nonhs_nodes
                    temp.clear();
                    for(int d : V[v]){
                        if( covered_by[d] == 0 ){
                            for( int u : sets[d] ){
                                hits_uncovered[u]--;
                                if(u != v && !was[u]) {
                                    was[u] = true;
                                    temp.push_back(u);
                                }
                            }
                        }
                    }
                    for( int d : temp ) {
                        was[d] = false;
                        addNonhsNode(d);
                        // conf_check[d] = true;
                    }
                    temp.clear();
                }

                in_hs[v] = true;
                for( int d : V[v] ){
                    if(covered_by[d] == 0) uncovered--;
                    covered_by[d]++;
                    covered_by_nodes[d].push_back(v);
                }

                if(uncovered == 0) setRemovedSetsHit();
                if(uncovered == 0 && removed_sets_hit) valid_state_change_history_marker.back() = true;

                // frozen[v] = true;
                frozen[v] = (rnd.nextInt(101) <= NODE_FREEZE_PROBAB);

                nodes_touched[v] = true;
                nodes_touched_with_neigh[v] = true;
                for (int d : cc_mark_neighborhoods[v]) nodes_touched_with_neigh[d] = true;

                if (!isRandomMoveCounterInValidInterval()) {
                    if(rnd.nextInt(5) > 0)
                        if(k_swaps == 1 && !allow_to_add_back_only_uncovered_cost_nodes)
                            for( int d : neigh_via_deg2_sets[v] ) if( in_hs[d] && V[d].size() == 2 ) {
                                if (!isForbiddenState( current_state_hash ^ hashes[d] ))
                                    nodes_to_remove.push_back(d);
                                for( int dd : neigh_via_deg2_sets[d] ) if( dd != v && !in_hs[dd] ) {
                                    if (!isForbiddenState( current_state_hash ^ hashes[dd] ))
                                        nodes_to_add_back.push_back(dd);
                                }
                            }

                    if(itr % 3 == 0)
                        if(k_swaps == 1 && !allow_to_add_back_only_uncovered_cost_nodes
                            && nodes_to_remove.empty() && nodes_to_add_back.empty()) {

                            bool b;
                            b = considerNodeDomination(v);

                            if (!b)
                            for ( int d : cc_mark_neighborhoods[v] ) if (in_hs[d]) {
                                b = considerNodeDomination(d);
                                if (b) {
                                    shuffle(cc_mark_neighborhoods[v],rnd);
                                    break;
                                }
                            }

                            // // if (!b) {
                            //     temp.clear();
                            //     for ( int d : V[v] ) for ( int dd : sets[d] ) if (in_hs[dd] && !was[dd] && dd != v) {
                            //         was[dd] = true;
                            //         temp.push_back(dd);
                            //         b = considerNodeDomination(dd);
                            //         // if (b) break;
                            //     }
                            //     for (int d : temp) was[d] = false;
                            // // }
                        }
                }

                if constexpr(use_cc) if ( use_cc_for_hs_nodes || use_cc_for_nonhs_nodes ) mark_cc(v); // #TEST
                if(last_node_removed != -1) conf_check[last_node_removed] = false;
                // if constexpr(use_cc) if ( use_cc_for_hs_nodes || use_cc_for_nonhs_nodes ) conf_check[v] = false;
            }
        } // for

        // if constexpr (!use_dynamic_sets)
        if (!use_dynamic_sets)
        if( !search_below_threshold )
        if( allow_to_add_back_only_uncovered_cost_nodes && !use_tabu_for_nonhs ) assert(uncovered == 0);

        // if(allow_to_add_back_only_uncovered_cost_nodes) ucn_alternation_countdown_arker--;
        // // if(!allow_to_add_back_only_uncovered_cost_nodes) ucn_alternation_countdown_arker--;

        ucn_alternation_countdown_marker--;

        if(uncovered == 0){
            if( 4*itr > iters )
                // if( (ucn_alternation_counter++ % ZERO_COST_VIOLATION_FREQENCY ) == 0 ){
                if( ((ucn_alternation_counter++ % ZERO_COST_VIOLATION_FREQENCY ) == 0) || ucn_alternation_countdown_marker == 0 ){
                    allow_to_add_back_only_uncovered_cost_nodes = !allow_to_add_back_only_uncovered_cost_nodes;
                    if constexpr(use_cc) //if( allow_to_add_back_only_uncovered_cost_nodes )
                    {
                        use_cc_for_nonhs_nodes = allow_to_add_back_only_uncovered_cost_nodes;
                        use_cc_for_hs_nodes = allow_to_add_back_only_uncovered_cost_nodes;
                        // fill(ALL(conf_check),false);
                        fill(ALL(conf_check),true);

                        // use_hsn_que = (rnd.nextInt(2) == 0 ); // original
                        use_hsn_que = !use_hsn_que; // #TEST

                        if (use_hsn_que) if( use_cc_for_hs_nodes ){
                            hsn_que.clear();
                            fill(ALL(hsn_que),false);
                            for( int d : perm ) if(in_hs[d]) {
                                in_hsn_que[d] = true;
                                hsn_que.push_back(d);
                            }
                        }

                        if(allow_to_add_back_only_uncovered_cost_nodes) {
                            nodes_to_remove.clear();
                            nodes_to_add_back.clear();
                        }

                        if(allow_to_add_back_only_uncovered_cost_nodes)
                            ucn_alternation_countdown_marker = 3*current_state_size;
                        else ucn_alternation_countdown_marker = -1;
                    }
                }
        }
        if(uncovered == 0) valid_state_change_history_marker.back() = true;
        // if constexpr (use_dynamic_sets) if( !removed_sets.empty() ) valid_state_change_history_marker.back() = false;
        if (use_dynamic_sets) {

            // if(uncovered == 0 && !removed_sets.empty()) setRemovedSetsHit();

            // if( !removed_sets.empty() ) valid_state_change_history_marker.back() = false;
            valid_state_change_history_marker.back() = ((uncovered == 0) && removed_sets_hit); // #TEST
            // if(uncovered == 0 && removed_sets_hit && !removed_sets.empty()) { // just for tests
            //     clog << endl << "FOUND VALID HS BEFORE ALL SETS ARE ADDED BACK" << endl;
            //     DEBUG(removed_sets.size());
            // }
        }
        is_below_threshold = (uncovered > 0);


        bool replace_valid_mask = (uncovered == 0);
        replace_valid_mask &= ( (last_valid_state_size > current_state_size)
                                || (latest_replacement++ % valid_solution_replacement_frequency) == 0 );
        // if constexpr (use_dynamic_sets) replace_valid_mask &= removed_sets.empty();
        if (use_dynamic_sets) replace_valid_mask &= removed_sets.empty();
        if(replace_valid_mask) {
            last_valid_state_size = current_state_size;
            if( current_state_size <= lower_bound ) break;
        }
    }

    valid_hs = changeInitHsToLastValidHs();

    if(removed_sets.empty())
    if( current_state_size != valid_hs.size() ) {
        if( !search_below_threshold || ( search_below_threshold && current_state_size+1 != valid_hs.size() ) ) {
            // if constexpr (use_dynamic_sets) {
            if (use_dynamic_sets) {
                int cnt = count(ALL(valid_state_change_history_marker),true);
                if constexpr (enable_logs) {
                    DEBUG(current_state_size);
                    DEBUG(valid_hs.size());
                    DEBUG(cnt);
                }
            }else {
                if constexpr (enable_logs) {
                    DEBUG(current_state_size);
                    DEBUG(valid_hs.size());
                }
                // assert( current_state_size == valid_hs.size() || current_state_size == valid_hs.size()+1 );
                // assert( abs(current_state_size - (int)valid_hs.size()) <= 1 );
            }
        }
    }
    // assert( current_state_size == valid_hs.size() || current_state_size == valid_hs.size()-1 );

    if constexpr (enable_logs) {
        DEBUG(iters);
        DEBUG(valid_hs.size());
        DEBUG(valid_hs_mask_replaced_times);

        double avg_cbn_elements_per_removal = 1.0 * total_cbn_remove_size / (1+total_cbn_iters);
        DEBUG(avg_cbn_elements_per_removal);
    }

    if(!sw.tle()) assert(sets.size() == S);
    assert( isCorrectHS(sets, valid_hs, hit_nodes) );
    assert(valid_hs.size() <= init_hs.size()); // this can fail is used dynamic sets...

    DEBUG(iters);
    DEBUG(use_tabu_for_nonhs);
    DEBUG(visited_states_set.size());

    int sets_always_hit = count(ALL(set_always_hit),true);
    DEBUG(sets_always_hit);
    always_hit_sets.clear();
    for (int i=0; i<S; i++) if (set_always_hit[i]) always_hit_sets.emplace_back( sets[i] );

    int nodes_touched_cnt = count(ALL(nodes_touched),true);
    DEBUG(nodes_touched_cnt);

    int nodes_touched_cnt_neigh = count(ALL(nodes_touched_with_neigh),true);
    DEBUG(nodes_touched_cnt_neigh);

    return valid_hs;
}



VI HittingSetLS::hsImprovementLS4SA(const int _iters, const int lower_bound) {

    if(sets.empty()) return {};
    if(hs.empty()) return hs;

    // const int iters = min( _iters, 3'000'000 );
    const int iters = min( 10 * (N+S), min( _iters, 3'000'000 ));

    int valid_hs_mask_replaced_times = 0;
    int last_valid_state_size = hs.size();
    constexpr int valid_solution_replacement_frequency = inf;
    int latest_replacement = 0;

    int uncovered = 0;
    in_hs = StandardUtils::toVB(N, hs);
    VI valid_hs = hs;
    VI init_hs = hs;
    int current_state_size = hs.size();
    VB valid_hs_mask = in_hs;

    // covered_by[i] is the number of elements from current hitting set that belong to sets[i]
    covered_by = VI(S,0);
    covered_by_nodes.resize(S);
    LL total_cbn_remove_size = 0;
    int total_cbn_iters = 0;

    for( int v : hs ) for( int d : V[v] ) {
        covered_by[d]++;
        covered_by_nodes[d].push_back(v);
    }
    for( int i=0; i<S; i++ ) if( covered_by[i] == 0 ) uncovered++;
    assert((uncovered == 0) && "Provided hs for improvement is not valid");

    if(hs.size() == 1) return hs;

    if constexpr (enable_logs) {
        DEBUG(N);
        DEBUG(S);
        DEBUG(iters);
        int total_elements_in_sets = accumulate(ALL(sets),0, [](int s, auto & v){return s + v.size();});
        DEBUG(total_elements_in_sets);
    }


    constexpr bool use_rss = true;


    VI all_nodes(N);
    iota(ALL(all_nodes),0);

    VI covers_alone(N,0); // the number of sets that a node covers ALONE (without any other node)
    for( int i=0; i<S; i++ ){ if(covered_by[i] == 1) for( int d : sets[i] ) if(in_hs[d]) covers_alone[d]++; }
    auto cmp_hs = [&]( const int a, const int b ){ return covers_alone[a] < covers_alone[b]; };
    Heap<int> hs_nodes( all_nodes,cmp_hs);
    for( int i=0; i<N; i++ ) if(!in_hs[i]) hs_nodes.removeFromHeap(i);


    VI & state_change_history = all_nodes;
    state_change_history.clear();
    state_change_history.reserve(2*iters);
    VB valid_state_change_history_marker;
    valid_state_change_history_marker.reserve(2*iters);
    auto addStateChangeToHistory = [&](int v) {
        state_change_history.push_back(v);
        valid_state_change_history_marker.push_back(false);
    };
    auto changeInitHsToLastValidHs = [&]() {
        int ind = -1;
        for( int i=0; i<valid_state_change_history_marker.size(); i++ ){
            if(valid_state_change_history_marker[i]) ind = i;
        }
        VB res(N);
        for(int d : init_hs) res[d] = true;
        for( int i=0; i<=ind; i++ ){ int v = state_change_history[i]; res[v] = !res[v]; }
        return StandardUtils::toVI(res);
    };

    if constexpr (enable_logs) {
        ENDL(1);
        DEBUG(hs.size());
        DEBUG(lower_bound);
        ENDL(1);
    }


    VI hits_uncovered(N,0); // number of uncovered sets that node hits
    for( int i=0; i<S; i++ ){ if(covered_by[i] == 0) for(int d : sets[i]) hits_uncovered[d]++; }

    RandomSelectionSet<long double> rss_hs(N);
    RandomSelectionSet<long double> rss_nonhs(N);

    constexpr long double SA_INIT_TEMP = 0.5; // works well
    constexpr long double SA_MIN_TEMP = 0.1; // works well
    constexpr long double SA_ALPHA = 0.999; // works well
    constexpr long double eps = 1e-8; // values -8 and -9 seem to work well

    long double SA_TEMP = SA_INIT_TEMP;
    // int SA_TEMP_CHANGE_FREQ =  1 + iters / ( log(SA_MIN_TEMP / SA_INIT_TEMP) / log(SA_ALPHA) );
    int SA_TEMP_CHANGE_FREQ =  max((long double)1.0,1.0*iters / ( log(SA_MIN_TEMP / SA_INIT_TEMP) / log(SA_ALPHA) ) );
    if constexpr (enable_logs) DEBUG2(iters,SA_TEMP_CHANGE_FREQ);
    if constexpr (enable_logs) DEBUG(1.0 * iters / SA_TEMP_CHANGE_FREQ); // number of times that temperature will be changes

    auto getHSNDeltaForSA = [&](int v) { return covers_alone[v]; };
    auto getHSNSelectionProbabilityRSS = [&](int v) {
        long double D = getHSNDeltaForSA(v) / SA_TEMP;
        if(D > 70) return eps;
        return exp(-D);
    };

    auto getNONHSNSelectionProbabilityRSS = [&](int v) {
        return pow( 2*hits_uncovered[v], 1.5 + 2.0 * ( SA_INIT_TEMP - SA_TEMP ) / ( SA_INIT_TEMP - SA_MIN_TEMP ) );
    };


    auto updateNodeSA = [&](int v) {
        if constexpr (!use_rss) return;

        if ( in_hs[v] ) {
            long double p = getHSNSelectionProbabilityRSS(v);
            // assert(p >= eps);
            rss_hs.set(v,max(p, eps) );
        }
        else {
            long double p = getNONHSNSelectionProbabilityRSS(v);
            // assert(p >= eps);
            rss_nonhs.set(v, max(p,eps) );
        }
    };
    auto changeSATemp = [&]() { SA_TEMP *= SA_ALPHA; };

    if constexpr (use_rss) {
        for ( int i=0; i<N; i++ ) {
            if (in_hs[i]) rss_hs.set( i, getHSNSelectionProbabilityRSS(i) );
            else rss_nonhs.set( i, getNONHSNSelectionProbabilityRSS(i) );
        }
    }

    auto getNodeToRemove = [&]() { if constexpr (use_rss) return rss_hs.getRandomElement(); };

    // greedily select the best node to add to current hs - the one that will cover greatest number of uncovered sets
    auto getNodeToAdd = [&]() { if constexpr (use_rss) return rss_nonhs.getRandomElement(); };

    VB was(N,false);
    VI temp;

    {
        for( int i=0; i<N; i++ ) hs_nodes.set(i,i);
        for (int i = 0; i < N; i++) if (!in_hs[i]) hs_nodes.removeFromHeap(i);
    }

    const double avg_elements_per_set = accumulate(ALL(sets), 0.0,
        [](double s, auto & v){return s + v.size();}) / sets.size();
    if constexpr (enable_logs) DEBUG(avg_elements_per_set);


    auto satest = [&]() {
        return;
        if (!use_rss) return;

        for ( int i=0; i<N; i++ ) { // just a test
            if (in_hs[i]) {
                assert(rss_nonhs.getProbab(i) == 0);
                assert(rss_hs.getProbab(i) > 0);
            }
            else {
                assert(rss_hs.getProbab(i) == 0);
                assert(rss_nonhs.getProbab(i) > 0);
            }
        }
    };

    for( int itr = 0; itr < iters; itr++ ) {
        if(SA_TEMP < SA_MIN_TEMP) break;
        if (itr > 0 && (itr % SA_TEMP_CHANGE_FREQ) == 0) changeSATemp();

        satest();

        if (false)
        if (itr <= SA_TEMP_CHANGE_FREQ) {
            if constexpr (enable_logs) {
                ENDL(3);
                clog << "PTR 1" << endl;
                for (int i=0; i<N; i++) {
                    double p = (in_hs[i] ? getHSNSelectionProbabilityRSS(i) : getNONHSNSelectionProbabilityRSS(i));
                    double p2 = ( in_hs[i] ? rss_hs.getProbab(i) : rss_nonhs.getProbab(i) );
                    if (in_hs[i]) {
                        clog << "Probability of selecting node " << i << " that is " << ( in_hs[i] ? "" : " not " )
                             << "in hs and" << endl;
                        clog << "\tcovers_alone: " << covers_alone[i] << ", hits_uncovered: " << hits_uncovered[i] << " --> ";
                        clog << p << "    (p2 check: " << p2 << ")" << endl;
                    }
                }
            }
        }


        // if(itr % 1000 == 0) clog << "\ritr #" << itr << flush; // uncomment this to enable logging process
        if( (itr & 255) == 0 ) if( sw.tle() ) break;

        satest();

        //******************************//****************************** removing node

        { // remove node from current hs
            int v = getNodeToRemove();
            if(v == -1) break; // emergency break... why it happens? dunno...
            // assert(v != -1);
            int C = 0;
            while( !in_hs[v] ) {
                if (use_rss) rss_hs.set(v,0);

                v = getNodeToRemove();
                if(v == -1) break; // emergency break... why it happens? dunno...
                // assert(v != -1);
                if( C++ > 10*(N+S) ) {
                    if constexpr (enable_logs) DEBUG(current_state_size);
                    int hs_size = 0;
                    for( int i=0; i<N; i++ ) hs_size += in_hs[i];
                    string message = "cannot find a node to remove";
                    message += ", current_state_size: " + to_string(current_state_size);
                    message += ", hs_size: " + to_string(hs_size);
                    // assert(false && message.c_str());
                    DEBUG(message);
                    // assert(false && ("cannot find a node to remove, current_state_size: "
                    //     + to_string(current_state_size) + ", hs_size: " + to_string(hs_size)) == "" );
                    exit(29);
                }
            }
            if(v == -1) break; // emergency break... why it happens? dunno...

            if (use_rss) rss_hs.set(v,0);
            assert(in_hs[v]);
            current_state_size--;

            hs_nodes.removeFromHeap(v); // need to do that before reducing [covered_by]
            covers_alone[v] = 0;

            in_hs[v] = false;
            updateNodeSA(v);

            satest();

            for( int d : V[v] ){
                covered_by[d]--;
                total_cbn_iters++;
                total_cbn_remove_size += covered_by_nodes[d].size();
                // covered_by_nodes[d].erase(v);
                auto fun = [&](int ind){ return covered_by_nodes[d][ind] == v; };
                REMCFUN( fun, covered_by_nodes[d] );
                if(covered_by[d] == 0) uncovered++;
            }


            { // updating hs_nodes other than v (v was updated earlier)
                temp.clear();
                for (int d : V[v]) {
                    if (covered_by[d] == 1) {
                        int u = *covered_by_nodes[d].begin();
                        if( !in_hs[u] ) continue;
                        if(!was[u]) {
                            was[u] = true;
                            temp.push_back(u);
                            hs_nodes.removeFromHeap(u);
                        }
                        covers_alone[u]++;
                    }
                }

                satest();
                for(int d : temp) {
                    was[d] = false;
                    hs_nodes.set(d,d);
                    updateNodeSA(d);
                    satest();
                }
                temp.clear();
            }

            satest();

            { // updating nonhs_nodes
                temp.clear();
                for(int d : V[v]){
                    if(covered_by[d] == 0) {
                        for (int u : sets[d]) {
                            if(!was[u]) {
                                was[u] = true;
                                temp.push_back(u);
                            }
                            hits_uncovered[u]++;
                        }
                    }
                }

                satest();

                for(int d : temp) {
                    was[d] = false;
                    satest();
                    updateNodeSA(d);
                    satest();
                }
                temp.clear();
            }

            satest();

            addStateChangeToHistory(v);
            updateNodeSA(v);

            satest();
        }

        satest();

        //******************************//****************************** adding node back

        bool add_back = (uncovered > 0 );
        if(add_back){ // add node to current hs

            int v = getNodeToAdd();

            if( v == -1 ) break;
            assert(!in_hs[v]);

            if (use_rss) rss_nonhs.set(v,0);

            assert(!in_hs[v]);
            current_state_size++;

            in_hs[v] = true;
            updateNodeSA(v);

            { // update hs_nodes
                temp.clear();
                for (int d : V[v]) {
                    if (covered_by[d] == 1) {
                        int u = *covered_by_nodes[d].begin();
                        if( !in_hs[u] ) continue;

                        if(!was[u]) {
                            was[u] = true;
                            temp.push_back(u);
                            hs_nodes.removeFromHeap(u);
                        }

                        covers_alone[u]--;
                    }else if( covered_by[d] == 0 ){
                        covers_alone[v]++;
                    }
                }

                for(int d : temp) {
                    was[d] = false;
                    hs_nodes.set(d,d);
                    updateNodeSA(d);
                }
                temp.clear();

                hs_nodes.set(v,v);
                addStateChangeToHistory(v);
            }

            {// udate nonhs_nodes
                temp.clear();
                for(int d : V[v]){
                    if( covered_by[d] == 0 ){
                        for( int u : sets[d] ){
                            hits_uncovered[u]--;
                            if(u != v && !was[u]) {
                                was[u] = true;
                                temp.push_back(u);
                            }
                        }
                    }
                }
                for( int d : temp ) {
                    was[d] = false;
                    updateNodeSA(d);
                }
                temp.clear();
            }

            in_hs[v] = true;
            for( int d : V[v] ){
                if(covered_by[d] == 0) uncovered--;
                covered_by[d]++;
                covered_by_nodes[d].push_back(v);
            }
            updateNodeSA(v);
        }

        satest();

        if(uncovered == 0) valid_state_change_history_marker.back() = true;

        bool replace_valid_mask = (uncovered == 0);
        replace_valid_mask &= ( (last_valid_state_size > current_state_size)
                                || (latest_replacement++ % valid_solution_replacement_frequency) == 0 );
        if(replace_valid_mask) {
            last_valid_state_size = current_state_size;
            if( current_state_size == lower_bound ) break;
        }
    }

    valid_hs = changeInitHsToLastValidHs();
    assert( current_state_size == valid_hs.size() );

    if constexpr (enable_logs) {
        DEBUG(iters);
        DEBUG(valid_hs_mask_replaced_times);

        double avg_cbn_elements_per_removal = 1.0 * total_cbn_remove_size / (1+total_cbn_iters);
        DEBUG(avg_cbn_elements_per_removal);
    }

    return valid_hs;
}

pair<VI,VVI> HSLS::hsImprovementLS(VVI sets, VI hs, VB hit_nodes, Stopwatch & sw, int iters, int lower_bound,
    bool reduce, bool use_tabu_for_nonhs, bool admit_using_sa, bool admit_using_dynamic_sets) {
    if (sets.empty()) return {};
    if ( hs.empty() ) assert(sets.empty() && "hs must be a valid hitting set of given sets");

    assert(iters >= 0);
    if (iters == 0) return {hs,{}};

    constexpr bool check_assertions = false;

    if(reduce) {
        int initN = -1;
        if constexpr (check_assertions) {
            int & N = initN;
            if(!hs.empty()) N = *max_element(ALL(hs))+1;
            for(auto & s : sets) for(auto d : s) N = max(N,d+1);
            assert(HittingSetLS::isCorrectHS(sets, hs));
        }

        sw.start("reduceForHSLS");
        HSLS hsls_red(sw,hit_nodes);
        auto [sets2, hs2, kernel] = hsls_red.reduceForHSLS(sets, hs);
        sw.stop("reduceForHSLS");
        if constexpr (enable_logs) DEBUG(kernel.size());

        if constexpr (check_assertions) {
            int N = 0;
            if(!hs2.empty()) N = *max_element(ALL(hs2))+1;
            if(!kernel.empty()) N = max(N,*max_element(ALL(kernel))+1);
            for(auto & s : sets) for(auto d : s) N = max(N,d+1);
            assert(HittingSetLS::isCorrectHS(sets2, hs2, N));
            assert(HittingSetLS::isCorrectHS(sets, hs2 + kernel, initN));
        }

        if( hs2.size() <= 4 ) return {hs2 + kernel,{}}; // #TEST - quite bad for small instance...

        lower_bound -= kernel.size();

        constexpr bool use_remapper = true;
        int N = 0;
        for(auto & s : sets2) for(auto d : s) N = max(N,d+1);
        VI mapper(N,0), remapper(N,0);

        if (use_remapper){
            VI zb; zb.reserve(N);
            VB was(N);
            for( auto & s : sets2 ) for(int d : s) if(!was[d]){ was[d] = true; zb.push_back(d); }
            for(int d : hs2) if(!was[d]){ was[d] = true; zb.push_back(d); }
            int cnt = 0;
            for( int d : zb ) {
                mapper[d] = cnt++;
                remapper[mapper[d]] = d;
            }

            for( auto & s : sets2 ) for( int & d : s ) d = mapper[d];
            for(auto & d : hs2) d = mapper[d];
        }else iota(ALL(remapper),0);

        lower_bound = 1;

        HittingSetLS hsls(sets2, hs2, hit_nodes, sw);
        VI res;
        res =  hsls.hsImprovementLS4(iters, lower_bound, use_tabu_for_nonhs);

        if (use_remapper) for(int & d : res) d = remapper[d];

        {
            auto zb = set(ALL(res));
            zb += kernel;
            res = VI(ALL(zb));
        }

        return {res,{}};
    }
    else {
        // auto init_sets = sets;

        auto &sets2 = sets;
        auto &hs2 = hs;
        auto hit_nodes2 = hit_nodes;

        constexpr bool use_remapper = true;
        // int N = 0;
        int N = *max_element(ALL(hs))+1;
        for(auto & s : sets2) for(auto d : s) N = max(N,d+1);
        VI mapper(N,-1), remapper(N,-1);

        if constexpr (use_remapper){
            VI zb; zb.reserve(N);
            VB was(N);
            for( auto & s : sets2 ) for(int d : s) if(!was[d]){ was[d] = true; zb.push_back(d); }
            for(int d : hs2) if(!was[d]){ was[d] = true; zb.push_back(d); }
            // sort(ALL(zb)); // how about sorting? It will preserve order, hence possibly preserving any 'locality'
            int cnt = 0;
            for( int d : zb ) {
                mapper[d] = cnt++;
                remapper[mapper[d]] = d;
            }

            for( auto & s : sets2 ) for( int & d : s ) d = mapper[d];
            for(auto & d : hs2) d = mapper[d];

            {
                fill(ALL(hit_nodes2),false);
                for ( int i=0; i<min(N,(int)hit_nodes.size()); i++ ) if (hit_nodes[i] && mapper[i] != -1
                    // && mapper[i] < hit_nodes2.size()
                    ) {
                    // assert(mapper[i] < hit_nodes2.size());
                    if( !( mapper[i] >= 0 && mapper[i] < hit_nodes2.size()) ) {
                        if constexpr (enable_logs) {
                            DEBUG(i); DEBUG(mapper[i]); DEBUG(cnt); DEBUG(hit_nodes.size()); DEBUG(hit_nodes2.size());
                            DEBUG(N); assert(mapper[i] >= 0 && mapper[i] < hit_nodes2.size());
                        }
                        assert(mapper[i] >= 0 && mapper[i] < hit_nodes2.size());
                    }
                    hit_nodes2[ mapper[i] ] = true;
                }
            }
        }else iota(ALL(remapper),0);

        // assert(hs.size() == set(ALL(hs)).size());

        HittingSetLS hsls(sets2, hs2, hit_nodes2, sw); // original
        // HittingSetLS2 hsls2(sets2, hs2, hit_nodes2, sw); // #TEST
        VI res;

        IntGenerator rnd;
        bool use_sa = false;
        // bool use_sa = true;
        // bool use_sa = (rnd.nextInt(2) == 0);
        // bool use_sa = (rnd.nextInt(3) == 0);

        if (admit_using_sa){
            double sa_probab = 0;
            // if( hs2.size() <= 10 ) sa_probab = 0.75;
            // else if( hs2.size() <= 50 ) sa_probab = 0.5;
            // else if( hs2.size() <= 100 ) sa_probab = 0.33;
            // else if( hs2.size() <= 200 ) sa_probab = 0.25;
            // else if( hs2.size() <= 300 ) sa_probab = 0.2;
            // else if( hs2.size() <= 500 ) sa_probab = 0.15;
            // else sa_probab = 0.1;

            // if( hs2.size() <= 100 ) sa_probab = 0.25;
            // else sa_probab = 0.1; // #TEST - use SA but very rarely...
            sa_probab = 0.1; // #TEST - use SA but very rarely...

            double r = 1.0 * rnd.nextInt(1e9) / (1e9-1);
            use_sa = ( r <= sa_probab );
        }

        use_sa = false;

        lower_bound = max(lower_bound,1);

        if (!use_sa ) res = hsls.hsImprovementLS4(iters, lower_bound, use_tabu_for_nonhs, admit_using_dynamic_sets);
        // if (!use_sa ) res = hsls2.hsImprovementLS4(iters, lower_bound, use_tabu_for_nonhs, admit_using_dynamic_sets); // #TEST
        else res = hsls.hsImprovementLS4SA(iters/2, lower_bound); // #TEST - use less iterations

        if constexpr (use_remapper) {
            for(int & d : res) d = remapper[d];
            for ( auto & v : hsls.always_hit_sets ) for (int & d : v) d = remapper[d];
        }

        // assert( HittingSetLS::isCorrectHS(init_sets, res, hit_nodes) );

        return {res,hsls.always_hit_sets};
    }
}