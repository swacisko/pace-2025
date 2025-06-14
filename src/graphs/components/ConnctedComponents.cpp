//
// Created by sylwester on 3/16/20.
//

#include <graphs/GraphUtils.h>
#include <graphs/components/ConnectedComponents.h>

#include "graphs/components/ConnectedComponents.h"


void ConnectedComponents::dfs(VVI& V, int &num, int &par, VB& was, VVI & comps){
    was[num] = true;
    comps.back().push_back(num);

    for( int t : V[num] ){
//        if( t < 0 ||  t >= V.size() ) exit(17);
        if( t != par && !was[t] ) dfs(V,t,num,was,comps);
    }

};

VVI ConnectedComponents::getConnectedComponents( VVI & V ){
    VVI comps;
    VB was(V.size(),false);

    for(int i=0; i<V.size(); i++){
        if(!was[i]){
            comps.push_back( getConnectedComponentForNode(V,i,was) );
        }
    }

    return comps;
}


VVI ConnectedComponents::getConnectedComponents( VVI &V, VI & S ){
    VVI comps;

    VB was(V.size(),false);
    for(int d : S) was[d] = true;

    for(int i=0; i<V.size(); i++){
        if(!was[i]){
            comps.push_back( getConnectedComponentForNode(V,i,was) );
        }
    }

    return comps;
}

VI ConnectedComponents::getConnectedComponentForNode(VVI &V, int v, VB &was) {

    // VI comp;
    // function< void(int,int) > dfsLambda = [&dfsLambda,&was,&V,&comp](int num, int par){
    //     if(was[num]) return;
    //     was[num] = true;
    //     comp.push_back(num);
    //     for( int t : V[num] ){
    //         if( t != par && !was[t] ) dfsLambda(t,num);
    //     }
    // };
    //
    // dfsLambda(v,v);

    VI comp(1,v);
    was[v] = true;
    for(int i=0; i<comp.size(); i++) {
        int v = comp[i];
        for(int d : V[v]) if(!was[d]) {
            was[d] = true;
            comp.push_back(d);
        }
    }


    return comp;
}

int ConnectedComponents::countEdgeWeightsInComponent(VVI &V, VVI &W, int v, VB &was) {
//    cerr << "ConnectedComponents::countEdgeWeightsInComponent NOT TESTED YET!" << endl;
    int weight = 0;
    function< void(int) > dfs = [&dfs,&V,&W,&was, &weight](int num){
        was[num] = true;
        for(int i=0; i<V[num].size(); i++){
            int d = V[num][i];
            if(!was[d]) weight += W[num][i];
        }

        for(int d : V[num]) if(!was[d]) dfs(d);
    };

    dfs(v);

    return weight;
}

VVI ConnectedComponents::getBiconnectedComponents(VVI &V) {
    constexpr bool debug = false;

    int N = V.size();

    VI tin(N,-1);
    VI low(N, 1e9);
    VB was(N,false);

    VVI aux_tree(N);
    VVI bicomponents;
    VI bicomp;

    function<void(int)> findBicomp = [&]( int u ){
        if(debug) clog << "\t\tfindBicomp, u: " << u << ", aux_tree[u]: " << aux_tree[u] << endl;
        bicomp.push_back(u);
        for( int d : aux_tree[u] ) findBicomp(d);
        aux_tree[u].clear(); // clearing auxiliary tree
    };

    int time_stamp = -1;
    function<void(int,int)> dfs = [&]( int u, int par ){
        if( debug ) clog << endl << "Visiting u: " << u << endl;
        was[u] = true;
        time_stamp++;
        tin[u] = time_stamp;
        low[u] = u;

        if(debug) clog << "tin: " << tin[u] << endl;

        for( int d : V[u] ){
            if( !was[d] ){
                dfs(d,u);
                if( low[d] == u ){
                    bicomp.clear();
                    if(debug) clog << endl << "u: " << u << ", d: " << d << "  --> FINDING BICOMPONENT" << endl;
                    findBicomp(u);
                    bicomponents.push_back(bicomp);
                    if(debug) ENDL(2);
                }
            }
        }

        for( int d : V[u] ){
            if( d != par ){
                if( tin[ low[u] ] > tin[low[d]] ) low[u] = low[d];
            }
        }

        if(debug) clog << "\tReturning, u: " << u << ", low: " << low[u] << ", tin: " << tin[u] << endl;

        aux_tree[low[u]].push_back(u);
    };

    for( int i=0; i<N; i++ ){
        if( !was[i] ) dfs(i,i);
    }

    fill(ALL(was),false);
    for(VI & cmp : bicomponents) for(int d : cmp) was[d] = true;
    for( int i=0; i<N; i++ ){
        if(!was[i]) bicomponents.push_back({i});
    }

    return bicomponents;
}
