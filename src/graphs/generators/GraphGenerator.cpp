//
// Created by sylwester on 8/8/19.
//

#include <graphs/generators/GraphGenerator.h>
#include <combinatorics/CombinatoricUtils.h>
#include <unordered_set>
#include <Constants.h>
#include <utils/RandomNumberGenerators.h>
#include <graphs/GraphUtils.h>
#include <utils/StandardUtils.h>

VVI GraphGenerator::getRandomGraph(int N, int M, bool directed) {
    VVI V(N);
    if( (LL)N*(N-1)/2 > 5*M ){ // in case of large graphs, i do by rand rather than storing the whole structure
        unordered_set<LL> edges;

        UniformIntGenerator gen( 0, (LL)N*(LL)N-1 );

        while( edges.size() < M ){
            long long e = gen.rand();
            long long a = e % N;
            long long b = e / N;
            if(a == b) continue;
            if( !directed && a > b ) swap(a,b);

            edges.insert( b*N+a );
        }

        for( LL p : edges ){
            int a = p % N;
            int b = p / N;
            V[a].push_back(b);
            if( !directed ) V[b].push_back(a);
        }

    }else{
        VPII edges;
        for(int i=0; i<N; i++){
            for(int k=i+1; k<N; k++){
                edges.push_back({i,k});
                if(directed) edges.push_back({k,i});
            }
        }

        UniformIntGenerator gen( 0, (LL)N*(LL)N-1 );
        StandardUtils::shuffle( edges, gen.getRNG() );

        for(int i=0; i<min( M, (int)edges.size() ); i++){
            int a = edges[i].first;
            int b = edges[i].second;
            V[a].push_back(b);
            if( !directed ) V[b].push_back(a);
        }
    }

    return V;
}

VVI GraphGenerator::getRandomGraph(int N, double p, bool directed) {
    VVI V(N);

    std::mt19937_64 rng;
    rng.seed(171);
    std::uniform_real_distribution<double> unif(0, 1);

    for( int i=0; i<N; i++ ){
        for(int k= ( directed ? 0 : i+1 ) ; k<N; k++){
            double currentRandomNumber = unif(rng);
            if( currentRandomNumber < p ){
                V[i].push_back(k);
                if(!directed) V[k].push_back(i);
            }
        }
    }

    return V;
}

VVI GraphGenerator::getRandomGraphAugmentedWithEdges(int N, int M, VPII LD) {
    VVI V = GraphGenerator::getRandomGraph(N,M);
    VPII ed = GraphUtils::getGraphEdges(V);
    set<PII> edges(ALL(ed));

    UniformIntGenerator rnd(0,N-1);

    for( auto & [L,D] : LD ){
        if(L <= 0 || L > N) continue;
        D = min(D,N-1);
        auto subs = CombinatoricUtils::getRandomSubset(N - 1, L);
        for (int u : subs) {
            int cnt = 0;
            while (cnt < D) {
                int v = rnd.rand();
                if (u == v) continue;
                edges.insert({u, v});
                edges.insert({v, u});
                cnt++;
            }
        }
    }

    V = VVI(N);
    for( auto & [a,b] : edges ){
        if( a < b ){
            V[a].push_back(b);
            V[b].push_back(a);
        }
    }

    return V;
}



VVI GraphGenerator::getRandomBipartiteGraph(int L, int R, int M ) {
    M = min(M,L*R);
    int N = L+R;
    VVI V(N);
    if( 1ll * N*(N-1)/2 > 5*M ){ // in case of large graphs, i do by rand rather than storing the whole structure
        set<PII> edges;
        UniformIntGenerator g( 0, N*N-1 );

        while( edges.size() < min( M, L*R ) ){
            int a = g.rand() % L;
            int b = L + g.rand() % R;

            edges.insert( {a,b} );
        }

        for( PII p : edges ){
            int a = p.first;
            int b = p.second;
            V[a].push_back(b);
            V[b].push_back(a);
        }

    }else{
        VPII edges;
        for(int i=0; i<L; i++){
            for(int k=L; k<N; k++){
                edges.push_back({i,k});
            }
        }

        UniformIntGenerator gen( 0, (LL)N*(LL)N-1 );
        StandardUtils::shuffle( edges, gen.getRNG() );

        for(int i=0; i< min(M,(int)edges.size()) ; i++){
            int a = edges[i].first;
            int b = edges[i].second;
            V[a].push_back(b);
            V[b].push_back(a);
        }
    }

    return V;
}


VVI GraphGenerator::getRandomBipartiteGraph(int L, int R, double p ) {
    int N = L+R;

    VVI V(N);

    std::mt19937_64 rng;
    rng.seed(171);
    std::uniform_real_distribution<double> unif(0, 1);

    for( int i=0; i<L; i++ ){
        for(int k= L; k<N; k++){
            double currentRandomNumber = unif(rng);
            if( currentRandomNumber < p ){
                V[i].push_back(k);
                V[k].push_back(i);
            }
        }
    }

    return V;
}

VVI GraphGenerator::getGrid(int rows, int columns) {
    VVI V( rows*columns );

    for( int i=0; i<columns; i++ ){
        if( i < columns-1 ){

            for( int j=0; j<rows; j++ ){
                int a = j*columns+i;
                int b = a+1;

                V[a].push_back(b);
                V[b].push_back(a);
            }

        }
    }


    for( int i=0; i<rows; i++ ){
        if( i < rows-1 ){

            for( int j=0; j<columns; j++ ){
                int a = i*columns+j;
                int b = a+columns;

                V[a].push_back(b);
                V[b].push_back(a);
            }

        }
    }

    return V;
}

VVI GraphGenerator::getRandomTreePrufer(int N) {
    if( N <= 1 ) return VVI(1);
    if( N == 2 ){ VVI V(2); V[0].PB(1); V[1].PB(0); return V;	}

    int INF = Constants::INF;

    VI last(N,-1); // ostatnie wystapienie liczby i w kodzie prufera jest na miejscu last[i]
    VI seq = CombinatoricUtils::getRandomSequence( N-1, N-2 ); // generuje kod prufera
    FORD( i,SIZE(seq)-1,0 ) if( last[ seq[i] ] == -1 ) last[ seq[i] ] = i;
    int p = 0,t = INF;
    VVI V(N);
    REP(i,SIZE(seq)){
        if( t == INF ) while( ( t = p ) < SIZE(last) && last[p++] != -1 );

        V[t].PB( seq[i] );
        V[seq[i]].PB(t);
        last[t] = INF;

        t = INF;
        if( i == last[ seq[i] ] ){
            last[ seq[i] ] = -1;
            if( seq[i] < p ){
                last[seq[i]] = INF;
                t = seq[i];
            }
        }
    }
    REP( i,SIZE(last) ) if( last[i] == -1 && i != seq[SIZE(seq)-1] ){ p = i; break;	}
    V[p].PB( seq[ SIZE(seq)-1 ] );
    V[ seq[ SIZE(seq)-1 ] ].PB(p);
    return V;
}

VVI GraphGenerator::getPath(int N, bool randomOrder) {
    VI perm = CombinatoricUtils::getRandomPermutation(N);
    if(!randomOrder) iota(ALL(perm), 0);
    VVI V(N);
    for( int i=1;  i<N; i++ ){
        int a = perm[i-1];
        int b = perm[i];
        V[a].push_back(b);
        V[b].push_back(a);
    }
    return V;
}

VVI GraphGenerator::getCycle(int N, bool randomOrder) {
    VI perm = CombinatoricUtils::getRandomPermutation(N);
    if( !randomOrder ) iota(ALL(perm),0);
    VVI V(N);
    for( int i=0, j=N-1;  i<N; j=i, i++ ){
        int a = perm[j];
        int b = perm[i];
        V[a].push_back(b);
        V[b].push_back(a);
    }
    return V;
}


VVI GraphGenerator::getUnionOfTriangles(int N, int triangles, bool directed) {
    VVI V(N);

    UniformIntGenerator rnd(0,N-1);
    set<PII> edges;
    while(triangles--){
        int a = rnd.rand();
        int b = rnd.rand();
        int c = rnd.rand();

        if( a == b || a == c || b == c ){ // we do not admit loops
            triangles++;
            continue;
        }

        edges.insert({a,b});
        edges.insert({b,c});
        edges.insert({c,a});

        if( !directed ){
            edges.insert({b,a});
            edges.insert({c,b});
            edges.insert({a,c});
        }
    }

    for( auto & [a,b] : edges ) V[a].push_back(b);
    return V;
}

VVI GraphGenerator::getStar(int N) {
    VVI V(N);
    for( int i=1; i<N; i++ ) GraphUtils::addEdge(V,0,i);
    return V;
}

VVI GraphGenerator::getRandomGraphNonuniform(int N, int M, VI probabs, bool directed) {
    LL S = accumulate(ALL(probabs),0ll);
    UniformIntGenerator rnd(0,S);

    M = min( (LL)M, 1ll * N * (N-1) / 2 );

    VLL pref(N);
    pref[0] = probabs[0];
    for(int i=1; i<N; i++) pref[i] = pref[i-1] + probabs[i];

    auto getRandomNode = [&](){
        LL r = rnd.rand();
        int ind = lower_bound(ALL(pref), r) - pref.begin();
        return ind;
    };

    set<PII> zb;

    while( zb.size() < M ){
        int a = getRandomNode();
        assert(a < N);
        int b = getRandomNode();
        assert(b < N);

        if( a == b ) continue;
        if( !directed ) if(a > b) swap(a,b);

        if( zb.count({a,b}) ) continue;

        zb.insert({a,b});
    }

    VVI V(N);
    for(auto [a,b] : zb){
        V[a].push_back(b);
        if(!directed) V[b].push_back(a);
    }

    return V;
}

VVI GraphGenerator::getClique(int N) {
    VVI V(N);
    for(int i=0; i<N; i++){
        V[i].reserve(N-1);
        for( int k=1; k<N; k++ ) GraphUtils::addEdge(V,i, (i+k)%N, true);
    }
    return V;
}


VVI GraphGenerator::getRandomKRegularGraph(int N, int K, int iters) {
    if( ! ((N%2 == 0) || (K%2 == 0) ) || N <= K ){
        clog << "Cannot create a " << K << "-regular graph with " << N << " nodes" << endl;
        clog << "Returning an empty graph" << endl;
        return {};
    }

    VVI V(N);
    for(int i=0; i<N; i++) V[i].reserve(K);

    if( K % 2 == 0 ){
        for( int i=0; i<N; i++ ){
            for( int j=1; j<=(K/2); j++ ) GraphUtils::addEdge(V,i, (i+j)%N);
        }
    }else{ // N is even

        VPII matching;
        int a = N - 1, b = 0;
        for (int i = 0; i < N / 2; i++) matching.emplace_back(a--, b++);
        int T = K;
        if (K > N / 2) T = N - 1 - K;

        while (V[0].size() < T) {
            for (auto &[a, b] : matching) {
                GraphUtils::addEdge(V, a, b);
                a = (a + 1) % N;
                b = (b + 1) % N;
            }
        }

        if (K > N / 2) {
            // created a random N-1-K regular graph, thius we need to remove all edges in that graph from full clique
            // to obtain a K regular graph
            VPII edges = GraphUtils::getGraphEdges(V);
            V = getClique(N);
            GraphUtils::removeEdges(V, edges);
        }
    }

    assert( GraphUtils::regularity(V) == K );
    assert( GraphUtils::isSimple(V));

    // making random changes
    VPII edges = GraphUtils::getGraphEdges(V);
    for(auto & [a,b] : edges) if(a>b) swap(a,b);

    set<PII> zb(ALL(edges));

    int E = edges.size();

    if(!edges.empty()) {
        UniformIntGenerator rnd(0, E - 1);
        if (iters == -1) iters = N * N;

        while (iters--) {
            int e1 = rnd.rand();
            int e2 = rnd.rand();

            if (e1 > e2) swap(e1, e2);

            auto[a, b] = edges[e1];
            auto[c, d] = edges[e2];

            int x = min(a, c);
            int y = max(a, c);
            a = x, c = y;

            x = min(b, d);
            y = max(b, d);
            b = x, d = y;

            if (a == c || a == d || b == c || b == d || zb.count({a, c}) || zb.count({b, d})) {
                continue;
            }

            zb.erase(edges[e1]);
            zb.erase(edges[e2]);

            swap(edges[e2], edges.back());
            edges.pop_back();

            swap(edges[e1], edges.back());
            edges.pop_back();


            edges.emplace_back(a, c);


            edges.emplace_back(b, d);

            zb.insert({a, c});
            zb.insert({b, d});
        }

        for (int i = 0; i < N; i++) V[i].clear();
        for (auto &[a, b] : edges) GraphUtils::addEdge(V, a, b);
    }

    assert( GraphUtils::regularity(V) == K );

    return V;
}


VVI GraphGenerator::getRandomKPartiteGraph(VI partition_sizes, int M) {
    int N = accumulate(ALL(partition_sizes),0);
    VVI V(N);

    VI ps;
    partial_sum(ALL(partition_sizes), back_inserter(ps));

    VI in_part(N);
    int id = 0;
    int p = 0;
    for( int i=0; i<N; i++ ){
        in_part[i] = p;
        id++;
        if( id == ps[p] ) p++;
    }

    LL totalE = 0; // total number of edges
    for( int i=0; i<partition_sizes.size(); i++ ) totalE += partition_sizes[i] * (N - partition_sizes[i]);
    totalE >>= 1;

    M = min((LL)M,totalE);

    if( totalE > 50ll*M ){
        UniformIntGenerator rnd(0,N-1);

        set<PII> zb;
        while(zb.size() < M){
            int a= rnd.rand();
            int b = rnd.rand();
            if(a>b) swap(a,b);
            if( in_part[a] == in_part[b] ) continue;
            if(zb.count({a,b})) continue;
            zb.insert({a,b});
        }

        for(auto & [a,b] : zb) GraphUtils::addEdge(V,a,b);

    }else{ // generate all edges
        VPII edges;
        for( int i=0; i<N; i++ ){
            for( int k=i+1; k<N; k++ ){
                if( in_part[i] == in_part[k] ) continue;
                edges.emplace_back(i,k);
            }
        }

        StandardUtils::shuffle(edges);
        if(edges.size() > M) edges.resize(M);
        else{
            clog << "Cannot create a " << partition_sizes.size() << "-partite graph with given partition sizes and "
                 << M << " edges, there are not enough edges even in a full graph! Creating a full graph with "
                 << edges.size() << " edges instead!" << endl;
        }

        for(auto & [a,b] : edges) GraphUtils::addEdge(V,a,b);
    }

    return V;
}

VVI GraphGenerator::createIsomorphic(VVI V) {
    int N = V.size();
    VI perm = CombinatoricUtils::getRandomPermutation(N);
    return GraphUtils::remapGraph(V, perm);
}



VVI GraphGenerator::getSpatialGraph(int N, int k, VPII coords, function<double(PII, PII)> dist, int rand_neighs,
                                    double sparsity) {
    assert( k < N );
    assert(coords.size()==N);

    vector<unordered_set<int>> edges(N);
    vector<pair<PII,int>> temp;
    for(int i=0; i<N; i++) temp.emplace_back(coords[i], i);

    for( int i=0; i<N; i++ ){
        clog << "\r#" << i << " / " << N << flush;
        PII pt = coords[i];

//        if( (i%3)==0 ) StandardUtils::shuffle(temp); // this is here to take random order of nodes within the same distance
//        sort(ALL(temp), [&](auto& a, auto & b){
//            return dist(pt,a.first) < dist(pt,b.first);
//        });
//        assert( temp[0].second == i || coords[temp[0].second] == coords[i] );

        { // faster than sort() - finding the first k+1 smallest elements
            nth_element(temp.begin(), temp.begin() + k, temp.end(), [&](auto &a, auto &b) {
                return dist(pt, a.first) < dist(pt, b.first);
            });
            sort(temp.begin(), temp.begin() + k + 1, [&](auto &a, auto &b) {
                return dist(pt, a.first) < dist(pt, b.first);
            });
        }

        auto to_check = StandardUtils::slice( temp, 1,k+1 );


        rand_neighs = min(k, rand_neighs);
        if(rand_neighs != 0){
            StandardUtils::shuffle(to_check);
            to_check.resize(rand_neighs);
        }else assert(to_check.size() == k);

        for( int j=0; j<to_check.size(); j++ ){
            int a = i, b = to_check[j].second;
            if(a == b) continue;

            if(a>b)swap(a,b);
//            edges.insert({a,b});
            edges[a].insert(b);
        }
    }

    VPII ed; ed.reserve( 5*N );
    for(int i=0; i<N; i++) for(int d : edges[i]) ed.emplace_back(i,d);

    assert(sparsity >= 0.0 && sparsity <= 1.0);
    if(sparsity < 1.0){
        StandardUtils::shuffle(ed);
        ed.resize( ceil(ed.size() * sparsity) );
    }

    VVI V(N);
    for( auto [a,b] : ed ) GraphUtils::addEdge(V,a,b);
    return V;
}

VVI GraphGenerator::getRandomClusteredGraph1( VI cluster_sizes, double p, double q) {
    int N = accumulate(ALL(cluster_sizes),0);
    VVI V(N);

    VI in_part(N);
    int id = 0;
    int x = 0;

    int C = cluster_sizes.size();
    VVI clusters(C);

    VI ps;
    partial_sum(ALL(cluster_sizes), back_inserter(ps));

    for( int i=0; i<N; i++ ){
        in_part[i] = x;
        clusters[x].push_back(i);

        id++;
        if( id == ps[x] ) x++;
    }

    for(int i=0; i<C; i++) assert(clusters[i].size() == cluster_sizes[i]);

    for( int i=0; i<C; i++ ){
        for( int j=i; j<C; j++ ){
            // creating edges between cluster i and j

            VPII possible_edges;
            if( i != j ){
                possible_edges = StandardUtils::product( clusters[i], clusters[j] );
                assert(possible_edges.size() == clusters[i].size() * clusters[j].size());
            }
            else{
                possible_edges.clear();
                for( int x : clusters[i] ) for( int y : clusters[j] ) if(x<y) possible_edges.emplace_back(x,y);
                assert(possible_edges.size() == (cluster_sizes[i] * (cluster_sizes[i]-1) / 2) );
            }
            StandardUtils::shuffle(possible_edges);

            int M;
            if( i == j ) M = round( p * possible_edges.size() );
            else M = round( q * possible_edges.size() );

            possible_edges.resize(M);

            for(auto & [a,b] : possible_edges) GraphUtils::addEdge(V,a,b);
        }
    }

    return V;
}

function<double(PII, PII)> GraphGenerator::getMetricForTorus(int minx, int maxx, int miny, int maxy,
                                                             function<double(PII, PII)> metric) {
    assert(maxx >= minx);
    assert(maxy >= miny);

    return [minx=minx, miny=miny, maxx=maxx, maxy=maxy, metric=metric](PII a, PII b){
        int W = maxx - minx;
        int H = maxy - miny;

        VPII pts = {
                {b.first, b.second},
                {b.first-W, b.second},
                {b.first+W, b.second},
                {b.first, b.second-H},
                {b.first, b.second+H}
        };

        /**
         * Selecting the point from [pts] that is closest to a
         */
        PII it = *min_element( ALL(pts), [&a, &metric]( PII p, PII q ){
            return metric( a,p ) < metric(a,q);
        } );

        /**
         * and returning the distance between point a and closest points in [pts] (the closest of 'images' of b)
         */
        return metric(a,it);
    };
}

function<double(PII, PII)> GraphGenerator::getEuclideanMetric() {
    clog << "CAUTION! - returning squared euclidean metric for faster comparison. Not for exact distances!!" << endl;

    return [](PII a, PII b){
//        return sqrt((1ll*a.first - b.first) * (1ll*a.first - b.first) + (1ll*a.second - b.second)*(1ll*a.second - b.second));

        // returning squared-euclidean metric
        return (1ll*a.first - b.first) * (1ll*a.first - b.first) + (1ll*a.second - b.second)*(1ll*a.second - b.second);
    };
}

function<double(PII, PII)> GraphGenerator::getEuclideanMetricOnTorus(int minx, int maxx, int miny, int maxy) {
   return getMetricForTorus(minx, maxx, miny, maxy, getEuclideanMetric());
}

function<double(PII, PII)> GraphGenerator::getManhattanMetric() {
    return [](PII a, PII b){
        return abs(a.first - b.first) + abs(a.second - b.second);
    };
}

function<double(PII, PII)> GraphGenerator::getManhattanMetricOnTours(int minx, int maxx, int miny, int maxy) {
    return getMetricForTorus(minx, maxx, miny, maxy, getManhattanMetric());
}

VVI GraphGenerator::expand(VVI V, bool vertical_expansion, bool cross_expansion, bool copy_expansion) {
    int N = V.size();
    VVI W(2*N);

    VPII edges = GraphUtils::getGraphEdges(V);

    auto mapId = [&](int a){ return N+a; };

    if( vertical_expansion ) for(int i=0; i<N; i++) GraphUtils::addEdge( W, i, mapId(i) );
    if( cross_expansion ) for(auto & [a,b] : edges) GraphUtils::addEdge( W, a, mapId(b) );
    if( copy_expansion ){
        for(auto & [a,b] : edges){
            GraphUtils::addEdge( W, a, b );
            GraphUtils::addEdge( W, mapId(a), mapId(b) );
        }
    }

    return W;
}

VVI GraphGenerator::mergeGraphs1(VVI V, VVI H, bool random_injection) {
    if( V.size() < H.size() ) swap(V,H);

    int N = V.size();
    VI inj;
    if(random_injection){
        inj = CombinatoricUtils::getRandomSubset(N-1, H.size());
        StandardUtils::shuffle(inj);
    }else{
        inj.resize(H.size());
        iota(ALL(inj),0);
    }

    VPII edges_H = GraphUtils::getGraphEdges(H);
    for( auto & [a,b] : edges_H ) GraphUtils::addEdge(V, inj[a], inj[b] );

    return GraphUtils::makeSimple(V);
}

VVI GraphGenerator::joinGraphs1(VVI &V, VVI &H, VPII join_points) {
    int N = V.size(), M = H.size(), P = join_points.size();

    int T = N+M-P;
    VB is_join_point_H(M,false);
    for( auto & [a,b] : join_points ) is_join_point_H[b] = true;

    int cnt = 0;
    VI mapper(M);
    for( auto & [a,b] : join_points ) mapper[b] = a;
    for( int i=0; i<M; i++ ) if( !is_join_point_H[i] ) mapper[i] = N + (cnt++);

    VVI W(T);
    W = mergeGraphs1(W,V,false); // adding structure of V

    for( int i=0; i<H.size(); i++ ){
        int a = mapper[i];
        for( int d : H[i] ){
            if(d < i) continue;
            int b = mapper[d];
            GraphUtils::addEdge(W,a,b);
        }
    }

    W = GraphUtils::makeSimple(W);

    return W;
}

VVI GraphGenerator::joinGraphs2(VVI &V, VVI &H, VPII join_edges) {
    int N = V.size();
    VVI W = joinGraphs1(V,H,{});
    for( auto & [a,b] : join_edges ) GraphUtils::addEdge(W, a, N+b);
    return W;
}



VVI GraphGenerator::getComplimentaryGraph(VVI &V) {
    auto getComplimentaryNodes = [&]( VVI & V, VI & nodes ){
        VB inNodes( V.size(),false );
        for(auto p : nodes) inNodes[p] = true;
        VI res;
        for( int i=0; i<V.size(); i++ ){
            if( !inNodes[i] ) res.push_back(i);
        }
        return res;
    };

    VVI V2(V.size());
    for( int i=0; i<V.size(); i++ ){
        VI tmp = V[i];
        tmp.push_back(i);
        sort(ALL(tmp));
        V2[i] = getComplimentaryNodes( V,tmp );
    }

    bool correct = true;
    for( int i=0; i<V.size(); i++ ){
        VB was(V.size(),false);
        for( int d : V[i] ) was[d] = true;
        for(int d : V2[i]) was[d] = true;
        if( V[i].size() + V2[i].size() != V.size() -1 ) correct = false;
        for(int k=0; k<V.size(); k++) if( k != i && !was[k]) correct = false;
    }

    assert(correct);
    return V2;
}
//
// VVI GraphGenerator::getCactus(VI cycle_sizes, VI tree_sizes, bool join_by_edge, bool add_dangling ) {
//
//     VVVI F; // all graphs, cycles and trees
//
//     for( int d : cycle_sizes ) F.push_back( getCycle(d) );
//     for( int d : tree_sizes ) F.push_back( getRandomTreePrufer(d) );
//     StandardUtils::shuffle( F );
//
//     UniformIntGenerator rnd(0, 1e9);
//
//     function<VVI(int,int)> createCactus = [&]( int a, int b ){
//         if( a == b ) return F[a];
//
//         int mid = (a+b) / 2;
//
//         VVI cactus1 = createCactus(a, mid);
//         VVI cactus2 = createCactus(mid+1,b);
//
//         int p = rnd.nextInt(cactus1.size());
//         int q = rnd.nextInt(cactus2.size());
//
// //        clog << "Cacti created for interval [" << a << "," << b << "]" << endl;
// //        DEBUG(cactus1);
// //        DEBUG(cactus2);
//
//         VVI cactus_join;
//         if(join_by_edge) cactus_join = joinGraphs2(cactus1, cactus2, {{p,q}});
//         else cactus_join = joinGraphs1( cactus1, cactus2, {{p,q}} );
//
//         if(add_dangling && !join_by_edge){
//             int x = rnd.nextInt( cactus_join.size() );
//             cactus_join[x].push_back( cactus_join.size() );
//             cactus_join.push_back({x});
//         }
//
// //        assert( IsItCactus::isCactus(cactus_join) );
//
//         return cactus_join;
//     };
//
//
//     VVI cact = createCactus(0,F.size()-1);
//     if(add_dangling || join_by_edge) assert( cact.size() == accumulate(ALL(cycle_sizes),0) + accumulate(ALL(tree_sizes),0) );
//
//     return cact;
// }
//
//


