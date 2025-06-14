//
// Created by sylwester on 3/16/20.
//

#ifndef ALGORITHMSPROJECT_CONNECTEDCOMPONENTS_H
#define ALGORITHMSPROJECT_CONNECTEDCOMPONENTS_H

#include "Makros.h"

namespace ConnectedComponents{

    extern void dfs(VVI& V, int &num, int &par, VB& was, VVI & comps);
    /**
     *
     * @param V
     * @param sep
     * @return connected components of given graph V
     */
    extern VVI getConnectedComponents( VVI & V );

    /**
     *
     * @param V
     * @param sep
     * @return connected components of graph V \ S
     */
    extern VVI getConnectedComponents( VVI &V, VI & S );

    /**
     *  CAUTION!
     *  Function modifies was array. Each visited node in the same component as v is marked true.
     * @param V
     * @param was
     * @return nodes is a connected component of graph V induced by nodes for which was[v] = true. This way we can easily adapt to many uses.
     */
    extern VI getConnectedComponentForNode(VVI &V, int v, VB &was);

    /**
     * CAUTION!
     *  Function modifies was array. Each visited node in the same component as v is marked true.
     *
     * @param V simple, undirected graph.
     * @param W weight must be symetric, that is w(a,b) == w(b,a) for all nodes a and b
     * @param v
     * @param was bitvector with false, if given node should be considered in graph V[was], true if it should not
     * @return sum of weights of edges in induced by was graph V[was] (induced by those nodes for which was[v] == false)
     * in component containing v
     */
    extern int countEdgeWeightsInComponent( VVI& V, VVI& W, int v, VB& was );


    /**
     * Creates and returns a set of biconnected components of graph [V].
     * Graph [V] need not be connected.
     * Works in O(E) time.
     */
    extern VVI getBiconnectedComponents(VVI & V);

}

#endif //ALGORITHMSPROJECT_CONNECTEDCOMPONENTS_H
