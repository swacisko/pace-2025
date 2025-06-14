//
// Created by sylwester on 8/8/19.
//

#ifndef ALGORITHMSPROJECT_GRAPHGENERATOR_H
#define ALGORITHMSPROJECT_GRAPHGENERATOR_H

#include "Makros.h"

class GraphGenerator {

public:

    /**
     * Creates graph G(N,M)
     * @param N
     * @param M
     * @param directed if true, then a directed graph is created, otherwise undirected
     * @return random graph with N vertices and M edges.
     */
    static VVI getRandomGraph(int N, int M, bool directed = false);

    /**
     * Creates random graph G(N,p)
     * @param N
     * @param p
     * @return random graph with N vertices, in which every edge hash probability p of being in that graph
     */
    static VVI getRandomGraph(int N, double p, bool directed = false);

    /**
     * First creates a random graph with N nodes and M edges.
     * Then, for each pair LD[i], selects LD[i].first nodes at random and for this node selects randomly
     * LD[i].second neighbors, then adds those edges (unless they are already present in the graph).
     */
    static VVI getRandomGraphAugmentedWithEdges( int N, int M, VPII LD );

    /**
     *
     * @param L
     * @param R
     * @param M
     * @return random bipartite graph with M edges, where the first L vertices are in first part, and last R are in second part of the bipartition
     */
    static VVI getRandomBipartiteGraph( int L, int R, int M );

    /**
     * Creates a random K-partite graph with M randomly chosen edges, where K = partition_sizes.size(). i-th partition of the graph will have
     * partition_sizes[i] nodes (mutually disjoint).
     */
    static VVI getRandomKPartiteGraph( VI partition_sizes, int M );

    /**
     * Creates a random graph with N nodes and M edges. Each edges is chosen as a pair of nodes. Nodes are selected
     * randomly with probability of choosing node v equal to probabs[v] / S, where S is the sum of elements in probabs.
     *
     * #CAUTION!! Edges are selected each time randomly. Expected time to create the graph is therefore
     * at least M * logM (according to the Coupon-collector problem it will be M*logM if probabilities are equal),
     * but it may MUCH MUCH SLOWER, if the probabilities have a very high variance and the graph is dense.
     */
    static VVI getRandomGraphNonuniform(int N, int M, VI probabs, bool directed = false);

    /**
     *
     * @param L
     * @param R
     * @param p
     * @param directed
     * @return random bipartite graph in which each edge is with probability p, where the first L vertices are in first part, and last R are in second part of the bipartition
     */
    static VVI getRandomBipartiteGraph( int L, int R, double p );

    /**
     * Creates and returns random grid with rows*columns nodes. Node in row r and column c will have id = r*rows + c
     * @param rows
     * @param columns
     * @return random grid with @{rows} rows and @{columns} columns.
     */
    static VVI getGrid(int rows, int columns );

    /**
     * Function generates random tree. In first step it generates random prufer code, then creates tree represented by that code.
     * @param N
     * @return random tree.
     */
    static VVI getRandomTreePrufer(int N);

    /**
     * Function creates and returns path on N vertices
     * @param N
     * @return path on N vertices
     */
    static VVI getPath(int N, bool randomOrder = true);

    /**
     * Creates and returns a cycle of length [N].  If [random_order] is true, then ids of nodes on the cycle will be
     * shuffled, otherwise they will be consecutive integers.
     * @param N
     */
    static VVI getCycle(int N, bool randomOrder = true);

    /**
     * Creates a graph by selecting randomly [triangles] triangles (a,b,c), then adding all edges of
     * those triangles to the graph
     *
     * @param directed if true, then directed edges will be added, otherwise undirected edges
     */
    static VVI getUnionOfTriangles(int N, int triangles, bool directed = false);

    /**
     * @return a start with N nodes, node 0 is the center of the star
     */
    static VVI getStar( int N );

    /**
     * Craetes and returns a full graph K_n
     */
    static VVI getClique(int N);

    /**
     * Creates a random k-regular graph.
     * #CAUTION! The condition for existance of k-regular graphs needs to be met, t
     * hat is N >= K+1 and  N*K == 0 (mod 2)
     *
     * If K is even, then we create an initial graph as a 'circulant' graph, by adding to each node i neighbors
     * (i+j) % N, for j =1,2,...,K/2.
     *
     * If K is odd, then N must be even. If K is small, then we create randomly K full matchings, then take a union
     * of those matchings. A matching is created by taking a random permutation of nodes, then taking edges as two
     * consecutive nodes.
     * If, however, K is large, then we first craete a clique K_N, then K times find a perfect matching in that graph,
     * and remove that matching. This way we will always find a K edge-disjoint matchings.
     *
     * After creating an initial graph, we consider [iters] (or N*N if [iters] is -1) pairs of present edges,
     * (a,b) and (c,d), then we change that pair to (a,c) and (b,d).
     *
     * @param N number of nodes
     * @param K degree of each vertex
     */
    static VVI getRandomKRegularGraph( int N, int K, int iters = -1 );

    /**
     * Expands the graph in the following way:
     * For each node v in V, two copies v1 and v2 will be created.
     *
     * If [vertical_expansion] is set false, then for each node a and edge (a1,a2) will be added to the graph.
     * If [cross_expansion] is set false, then for each edge (a,b) also edges (a1,b2), (a2,b1) will be added.
     * If [copy_expansion] is set false, then for each edge (a,b) also edges (a1,b1), (a2,b2) will be added.
     */
    static VVI expand( VVI V, bool vertical_expansion, bool cross_expansion, bool copy_expansion );




    /**
     * Creates an isomorphic graph, by taking a random permutation, then changing ids.
     */
    static VVI createIsomorphic(VVI V);

    /**
     * Makes a union of two given graphs.
     * In the first step the smaller graph with n nodes will be mapped to the larger graph with N >= n nodes. This is
     * done by remapping nodes using some injection [n] -> [N].
     * If [random_injection] is set true, then we use a random injection. Otherwise we we identity x -> x
     *
     * Then, in the resulting graph, an edge will be present if it is present in either of two graphs (the larger one,
     * or the smaller one mapped to the larger size).
     */
    static VVI mergeGraphs1( VVI V, VVI H, bool random_injection );

    /**
     * Based on graphs [V] and [H], creates a new graph such that, node join_points[i].first from V
     * and node join_points[i].second from H are identified, the rest are kept as new copies.
     *
     * e.g if V = a->b->c and H = x->y->z and join_points is {a,y}, then we obtain a graph
     * (x,t), (t,z), (t,b), (b,c)
     *
     * If [join_points] is empty, then we simply add H to V as a new copy, completely disconnected from V.
     *
     * #CAUTION! IDs of nodes may be completely shuffled during the process, only the structure will remain as should.
     *
     * @param join_points must be a vector of pairs (a,b) where a is a node from V and b is a node from H.
     * From each graph single node can occur in at most one point.
     */
    static VVI joinGraphs1( VVI & V, VVI & H, VPII join_points );

    /**
     * Based on graphs V and H, a new graph is created by taking separate copies of V and H and adding additionally
     * edges between nodes join_edges[i].first from V and join_edges[i].second from H.
     *
     * This is similar to [joinGraphs1], but instead of identifying nodes, we connect them simply by some additional
     * edges.
     */
    static VVI joinGraphs2( VVI & V, VVI & H, VPII join_edges );

    /**
     * Creates a disjoint union of given two graphs.
     */
    static VVI disjointUnion(VVI & V, VVI & H){ return joinGraphs2(V,H,{}); }

    /**
     * Creates a graph by taking N points on a plane with integer coordinates.
     * -10^9 \leq \leq x,y \leq 10^9. Then, for each node v, chooses k nodes that are closest to this node and edge
     * between node v and those closest nodes will be added to the graph.
     * Note, that edges may repeat for different v.
     *
     * Uses function [dist] to calculate the distance between two points.
     *
     * Generating takes time at least O( N^2 * log(N) ) - for each node v we sort all other nodes using [dist] function
     *
     * If [rand_neighs] > 0, the from closest k neighbors of each node we will select random [rand_neighs] nodes to
     * add connections between. This may be used to try to 'sparsify' clique that usually are created if we add all
     * connections for closest neighborhoods
     *
     * After the graph is created, only [sparsity] percentage of randomly chosen edges will be retained in the graph.
     */
    static VVI getSpatialGraph(int N, int k, VPII coords, function<double(PII, PII)> dist, int rand_neighs = 0,
                               double sparsity = 1.0 );

    /**
     * The following functions create and return functions calculating distances between two points (x1,y1), (x2,y2).
     * In case of calculating distances on Torus, the bounding rectangle needs to be provided as well.
     */
    static function<double(PII, PII)> getEuclideanMetric();
    static function<double(PII, PII)> getEuclideanMetricOnTorus(int minx, int maxx, int miny, int maxy);
    static function<double(PII, PII)> getManhattanMetric();
    static function<double(PII, PII)> getManhattanMetricOnTours(int minx, int maxx, int miny, int maxy);

    /**
     * Transforms given [metric] to work on torus. This is done by considering for a pair (a,b) 5 points:
     * (a,b), (a+W,b), (a-W,b), (a,b+H), (a,b-H)
     * @param metric metric for which corresponding metric on torus should be returned
     */
    static function<double(PII, PII)> getMetricForTorus(int minx, int maxx, int miny, int maxy, function<double(PII, PII)> metric);


    /**
     * Creates a random 'clustered' graph.
     * That is, there will be cluster_sizes.size() 'clusters'.
     * An edge (a,b) with nodes in the same cluster will 'have probability p' - for a cluster of size C, exactly
     * p*C*(C-1)/2 random edges will be selected.
     *
     * An edge with ends in different clusters will 'have probability q' - if there are X such possible edges, then
     * q*X of them will be chosen randomly.
     *
     * By selecting edges this way, we ensure that there are no 'large' deviations for small graphs/clusters and
     * that time complexity remains roughly O(E), where E is the total number of edges, hence large sparse graphs can
     * be created this way.
     *
     * #CAUTION!! Current implementation works in time O(N^2) !!
     */
    static VVI getRandomClusteredGraph1(VI cluster_sizes, double p, double q );

    /**
     * Functions turns an undirected graph [V] into DAG, using a following approach:
     * For each edge (a,b) in [V], an arc a-> is added to the DAG if fun(a,b) will return 0,
     * arc b->a will be added if fun(a,b) returns 1 and both arcs will be added if fun(a,b)
     * returns 2.
     */
    template<class _F>
    static VVI turnIntoDAGforSequence( VVI & V, _F fun ){
        int N = V.size();
        VVI dag(N);
        for( int a=0; a<N; a++ ){
            for( int b : V[a] ){
                if( b < a ) continue;
                int opt = fun(a,b);
                if( opt == 0 ) dag[a].push_back(b);
                else if( opt == 1 ) dag[b].push_back(a);
                else{
                    dag[a].push_back(b);
                    dag[b].push_back(a);
                }
            }
        }

        return dag;
    }


    /**
     * Function creates and returns complementary graph.
     */
    static VVI getComplimentaryGraph( VVI & V );

    /**
     * Function creates a cactus graph. For each integer a in [cycle_sizes], there will be a cycle created of that size
     * in the cactus.
     * Analogically for [tree_sizes] - trees of that size will be created.
     *
     * All cycles and trees are then taken as a family of graphs F and the cactus is created as follows:
     * 1. We partition S in two halves. For each half we create a cactus recursively.
     * 2. We merge two cacti from the two halves using [joinGraphs1] function with a single join point pair (a,b),
     * where a is a random node from the first cactus and b is a random node from the second cactus.
     *
     * Additionally, if [add_dangling] is true then whenever we use [joinGraphs1] operation, we add a single 'dangling'
     * node, so that the total number of nodes in the final graph is equal to sum(cycle_sizes) + sum(tree_sizes)
     *
     * If [join_by_edge] is true, then instead of using [joinGraphs1] we will use [joinGraphs2] and join two
     * cacti by random edge. This way two biconnected components will never share a vertex. If [join_by_edge] is set
     * to true, then [add_dangling] will have no effect - no dangling nodes will be added, as size will be preserved.
     */
    static VVI getCactus( VI cycle_sizes, VI tree_sizes, bool join_by_edge = false, bool add_dangling = true );


    /**
     * Function creates a weighted, directed graph that can be used to verify the efficiency of used SSSP algorithm or
     * test if e.g. Dijkstra was correctly implemented.
     *
     * For incorrectly implemented Dijkstra or SPFA, this graph should make those algorithms run in O(N^2 * C) time.
     * This gets O(M*N) running time. C should be <= N/2, but C = 1 should work well enough anyway
     *
     * Constructed graph will have roughly not more than C*N + N/2 arcs.
     * Weights of arcs are from range [0, 3*N]
     *
     * @return pair (V,beg), where V is the structure of hte graph in VVPII format and beg is the starting vertex
     */
    static pair<VVPII,int> getSSSPMultirelaxationGraph(int N, int C = 1 );
};


#endif //ALGORITHMSPROJECT_GRAPHGENERATOR_H
