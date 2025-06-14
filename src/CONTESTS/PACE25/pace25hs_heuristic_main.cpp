//
// Created by sylwe on 04/03/2025.
//

#include <GraphInducer.h>
#include <GraphUtils.h>
#include <Stopwatch.h>

#include "DSSE.h"
#include "HittingSetLS.h"
#include "Makros.h"
#include "StandardUtils.h"
#include "CollectionOperators.h"


VVI readInput(){
    string s;

    int N,M;
    VVI sets;

    auto isNonnegativeInteger = [&](const string & s) {
        for(const auto & c : s) if(!isdigit(c)) return false;
        return true;
    };

    while( getline(cin,s) ){
        if( s.starts_with('c') ) continue;

        if(s.starts_with('p')){
            auto tokens = StandardUtils::split(s);
            N = stoi(tokens[2]);
            M = stoi(tokens[3]);
        }else {
            assert(!s.starts_with('c') && "read comment line instead of a set to hit, fix input reading method!");
            auto tokens = StandardUtils::split(s);
            VI zb(tokens.size());
            for(int i=0; i<tokens.size(); i++) assert( isNonnegativeInteger(tokens[i]) );
            for(int i=0; i<tokens.size(); i++) zb[i] = stoi(tokens[i]);
            sort(ALL(zb));
            sets.emplace_back( move(zb) );
        }
    }

    return sets;
}


VI shiftSolution(VVI & V, int N, VI & res) {
    clog << "Before shifting res.size(): " << res.size() << endl;
    VI to_add;
    VB in_res(N);
    for(int d : res) if(d < N) in_res[d] = true;
    for( int d : res ) if( d >= N ) {
        bool has = false;
        for( int dd : V[d] ) has |= in_res[dd];
        if(!has && !V[d].empty()) {
            int x = V[d][0];
            assert(x < N);
            in_res[x] = true;
        }
        // in_res[d] = false;
    }
    res = StandardUtils::toVI(in_res);
    clog << "\tto_add.size(): " << to_add.size() << endl;
    clog << "\tAfter shifting res.size(): " << res.size() << endl;
    return res;
}



auto solve2(int N, VVI &sets, const int time_limit_millis, bool exact_track) {
    Stopwatch sw;
    sw.setLimit("main", time_limit_millis);
    sw.start("main");

    int S = sets.size();
    VVI V(N+S);
    VB hit_nodes(N+S);
    VB excluded_nodes(N+S);

    for( int i=0; i<sets.size(); i++ ) {
        for( int d : sets[i] ) {
            V[d].push_back(N+i);
            V[N+i].push_back(d);
        }
    }

    if constexpr (enable_logs) DEBUG(V.size());
    if constexpr (enable_logs) DEBUG(GraphUtils::countEdges(V));

    for(int i=0; i<N; i++) hit_nodes[i] = true;
    for(int i=N; i<S+N; i++) excluded_nodes[i] = true;

    VI res;
    if(exact_track) {
        DSSE dsse(V,hit_nodes, excluded_nodes);
        dsse.exact_hs_solving_method = CPSAT;
        dsse.reductions_time_liimt = time_limit_millis / 20;
        res = dsse.solve(true,true,false);
    }else {
        DSS dss(sw, hit_nodes, excluded_nodes);
        dss.hs_track = true;
        res = dss.solveH(V,1,true, 0.99 * time_limit_millis, true,true);
    }

    shiftSolution(V,N,res);

    for(int d : res) {
        assert(d < N && "this does not need to hold if shifting was used (should not be necessary if optimum was found");
    }

    sw.stop("main");
    if constexpr (enable_logs) sw.writeAll();

    for(int d : res) assert(d < N);

    return res;
}



int main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0);

    addSigtermCheck();

    constexpr bool write_result = true;
    bool exact_track = false;

    Stopwatch starter;
    string input_reader_opt = "input reader";
    starter.start(input_reader_opt);

    if(write_result && !exact_track) clog.rdbuf(nullptr);

    auto sets = readInput();
    int S = sets.size();
    int N = 0;
    for( auto & v : sets) for(int d : v) N = max(N,d);
    for( auto & v : sets) for(int & d : v) d--;
    for( auto & v : sets) assert(!v.empty());

    clog << "Before remapping: " << endl;
    DEBUG(N);
    DEBUG(S);

    VI mapper(N,-1);
    VI remapper(N,-1);
    {
        set<int> zb;
        for( auto & v : sets ) zb.insert(ALL(v));
        int cnt = 0;
        for( int d : zb ) {
            remapper[cnt] = d;
            mapper[d] = cnt++;
        }
        N = cnt;
        for( auto & v : sets ) for(int & d : v) d = mapper[d];
    }

    clog << "After remapping: " << endl;
    DEBUG(N);
    DEBUG(S);


    int time_limit_millis = 90'000;

    if(write_result) time_limit_millis = 290'000;

    clog << "Reading input took " << starter.getTime(input_reader_opt) / 1000 << " sec." << endl;
    time_limit_millis -= starter.getTime(input_reader_opt);

    time_limit_millis *= 0.99; // take off 1% to finish all necessary computation and hopefully fit in the time limit

    // auto res = solve1(N,sets, time_limit_millis);
    auto res = solve2(N,sets, time_limit_millis, exact_track);

    for(auto & r : res) r = remapper[r];
    for(auto & v : sets) for(int & d : v) d = remapper[d];
    assert( HSLS::isCorrectHS(sets,res) );

    cout << res.size() << "\n";
    if (write_result) {
        for( int d : res ) cout << d+1 << "\n"; cout << flush;
    }
    return 0;
}