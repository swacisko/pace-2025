//
// Created by sylwe on 05/05/2025.
//

#include "GraphRemapper.h"

#include <FAU.h>
#include <GraphInducer.h>
#include <GraphUtils.h>
#include <StandardUtils.h>
#include <components/ConnectedComponents.h>

#include "CollectionOperators.h"


VI GraphRemapper::findDistances(VVI & V, int beg) {
    int N = V.size();
    VI dst(N, inf);
    dst[beg] = 0;
    VI neigh; neigh.reserve(N);
    neigh.push_back(beg);
    VB was(N);

    for( int i=0; i<neigh.size(); i++ ) {
        int v = neigh[i];
        was[v] = true;
        for(int d : V[v]) if(!was[d]) {
            was[d] = true;
            neigh.push_back(d);
            dst[d] = dst[v]+1;
        }
    }

    return dst;
}


VI GraphRemapper::optimizeOrder(VVI & V, VI order) {
    constexpr bool debug = false;

    int N = V.size();

    int firstInOrder = order[0];
    assert( order.size() == N );

    VVI traverseGraph(N);
    VI edgesInComp(N,0);
    VI firstInComp(N,0); // first in comp[ fau.Find(i) ] is the first node in @{order} in component that contains i, in given phase of the algorithm
    VI inOrder(N,0);
    for( int i=0; i<order.size(); i++ ) inOrder[ order[i] ] = i;

    FAU fau(N);

    if constexpr(debug)DEBUG(order);

    while( !order.empty() ){
        int p = order.back();
        order.pop_back();

        if(debug) cerr << "Adding " << p << endl;

        set<int> neigh;
        int edges = 0;
        for( int d : V[p] ){
            if( inOrder[d] > inOrder[p] ){
                int t = fau.Find(d);
                neigh.insert( t );
                edges++;
            }
        }

        if constexpr(debug) {cerr << "neigh: "; for(int t : neigh) cerr << t << " "; cerr << endl;}
        for( int d : neigh ) edges += edgesInComp[d];
        if constexpr(debug)DEBUG(edges);

        VI neighOrder(ALL(neigh));
        sort( ALL(neighOrder), [&edgesInComp]( int a, int b ){ return edgesInComp[a] < edgesInComp[b]; } );

        if constexpr(debug){
            DEBUG(neighOrder);
            cerr << "first in orders: "; for(int t : neighOrder) cerr << firstInComp[t] << " "; cerr << endl;
        }

        for( int d : neighOrder ) traverseGraph[p].push_back( firstInComp[d] );
        for( int d : neighOrder ) fau.Union(p,d);
        firstInComp[ fau.Find(p) ] = p;
        edgesInComp[ fau.Find(p) ] = edges;

        if constexpr(debug)ENDL(1);
    }

    if constexpr(debug) DEBUG(traverseGraph);

    VI newOrder;

    function< void(int) > restoreNewOrder = [&traverseGraph, &newOrder, &restoreNewOrder](int v){
        for( int d : traverseGraph[v] ){
            newOrder.push_back(d);
            restoreNewOrder(d);
        }
    };

    newOrder.push_back( firstInOrder );
    restoreNewOrder( firstInOrder );

    if constexpr(debug) {
        DEBUG(newOrder);
        exit(1);
    }

    return newOrder;
}

tuple<VVI, VI> GraphRemapper::remapGraph(VVI & V, VI& order) {
    int N = V.size();
    VI mapper(N), remapper(N);

    for( int i=0; i<N; i++ ) mapper[order[i]] = i;

    VVI W(N);
    for( int i=0; i<N; i++ ) W[mapper[i]].reserve(V[i].size());
    for( int i=0; i<N; i++ ) for( int d : V[i] ) W[mapper[i]].push_back(mapper[d]);

    return {W,mapper};
}

VI GraphRemapper::createRemappingNodeOrder(VVI & V) {
    constexpr bool debug = false;

    if(!GraphUtils::isConnected(V)) {
        // clog << "Creating order for disconnected graph" << endl;

        VI order;
        auto comps = ConnectedComponents::getConnectedComponents(V);
        sort(ALL(comps), [&](auto & v1, auto & v2){ return v1.size() > v2.size(); }  );

        int sum_sizes = 0;
        for( auto & cmp : comps ) {
            sum_sizes += cmp.size();

            if( cmp.size() == 1 ) order.push_back(cmp[0]);
            else {
                auto g = GraphInducer::induce(V,cmp);
                auto ord = createRemappingNodeOrder(g.V);
                g.remapNodes(ord);
                order += ord;
            }
        }

        assert(sum_sizes == V.size());
        assert(order.size() == V.size());

        return order;
    }

    int N = V.size();
    int M = GraphUtils::countEdges(V);
    // clog << "Creating order for connected graph, N: " << N << ", M: " << M << endl;


    VI deg_in_S(N,0);
    VB processed(N,false);

    int vs = -1, vt = -1;
    { // landmark-based selection
        auto dst0 = findDistances(V, 0);
        vs = 0;
        for( int i=0; i<N; i++ ) if( dst0[i] >= dst0[vs] ) vs = i;

        dst0 = findDistances(V, vs);
        vt = vs;
        for( int i=0; i<N; i++ ) if( dst0[i] > dst0[vt] ) vt = i;
    }

    auto dstvs = findDistances(V, vs);
    auto dstvt = findDistances(V, vt);

    VB is_outside(N,true);
    VB visited(N,false);

    auto cmp = [&](int a, int b) -> bool {
        if( deg_in_S[a] != deg_in_S[b] ) return deg_in_S[a] > deg_in_S[b];
        if( V[a].size() != V[b].size() ) return V[a].size() < V[b].size();
        if( dstvt[a] - dstvs[a] != dstvt[b] - dstvs[b] ) return dstvt[a] - dstvs[a] > dstvt[b] - dstvs[b];
        return a < b;
    };

    set<int, decltype(cmp)> zb(cmp);
    for( int i=0; i<N; i++ ) zb.insert(i);

    auto getNextNode = [&]()->int { return *zb.begin(); };

    VI order;
    VI tmp;
    tmp.reserve(N);

    auto addNode = [&](int v) {
        zb.erase(v);
        order.push_back(v);
        processed[v] = true;
        tmp.clear();
        for( int d : V[v] ) if(!processed[d]) {
            tmp.push_back(d);
            zb.erase(d);
        }
        for( int d : V[v] ) deg_in_S[d]++;
        for( int d : tmp ) zb.insert(d);
    };

    addNode(vs);

    while( order.size() < N ) { // graph must be connected
        int v = getNextNode();
        addNode(v);
    }

    VI optimized_order = optimizeOrder(V,order);
    order = optimized_order;

    assert(order.size() == N);

    return order;
}
