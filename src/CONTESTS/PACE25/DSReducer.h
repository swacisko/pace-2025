//
// Created by sylwe on 07/05/2025.
//

#ifndef DSREDUCER_H
#define DSREDUCER_H

#include <Stopwatch.h>

#include "Makros.h"
#include "StandardUtils.h"


class LiftableRule {
public:
    virtual ~LiftableRule() = default;
    virtual void lift(VB & res) = 0;
    virtual string getName() = 0;
    virtual bool affectsNode(int v) = 0;
    virtual string getDescription() = 0;

    static map<string,int> getReductionsFrequencies(auto & rules) {
        map<string,int> res;
        for ( auto r : rules ) res[r->getName()]++;
        return res;
    }

    static void liftSolution( vector<LiftableRule*> & rules, VB & res, bool delete_rules = false ) {
        for( auto * r : rules ) r->lift(res);
        if(delete_rules) for( auto * r : rules ) delete r;
    }
};

struct ReducibleRule : public LiftableRule {
    explicit ReducibleRule(int vv) : v(vv){}
    int v;
    void lift(VB & res) override { assert(v >= 0 && v < res.size()); res[v] = true; }
    string getName() override{ return "reducible"; }
    bool affectsNode(int v) override { return this->v == v; }
    string getDescription() override{ return "reducible rule, v: " + to_string(v); }
};

struct DomRed : public LiftableRule {
    DomRed( int vv, int ww ) : v(vv), swap_to(ww) {}
    int v, swap_to;
    // VI dominators; // this is just for tests

    void lift(VB & res) override {
        assert(v >= 0 && v < res.size());
        assert(swap_to >= 0 && swap_to < res.size());
        if( res[v] ) {
            res[v] = false;
            res[swap_to] = true;
        }
    }
    string getName() override{ return "dom"; }
    bool affectsNode(int v) override { return (this->v == v) || (swap_to == v); }
    string getDescription() override{ return "DomRed rule, v: " + to_string(v) + ", swap_to: " + to_string(swap_to); }
};

struct DomRed2 : public LiftableRule {
    DomRed2( PII gn, PII ngh, bool adj ) : gadget_nodes(gn), neigh(ngh), uv_adj(adj) {}
    PII gadget_nodes;
    PII neigh;
    bool uv_adj = false;

    void lift(VB & res) override {
        auto [a,b] = gadget_nodes;
        auto [u,v] = neigh;

        assert( a != b && a != u && a != v && b != u && b != v && u != v );

        if( !res[u] && !res[v] ) assert( res[a] && res[b] );
        if( res[u] || res[v] ) assert( !res[a] || !res[b] );
        if( res[u] && res[v] ) assert( !res[a] && !res[b] );

        if( res[a] || res[b] ) {
            res[a] = res[b] = false;
            if( !res[u] && !res[v] ) {
                if(uv_adj) res[u] = true;
                else res[u] = res[v] = true;
            }else {
                if( res[u] && !uv_adj ) res[v] = true;
                if( res[v] && !uv_adj ) res[u] = true;
            }
        }
    }
    string getName() override{ return "dom2"; }
    bool affectsNode(int v) override {
        bool r = false;
        auto [a,b] = gadget_nodes;
        r |= ( v == a || v == b );
        tie(a,b) = neigh;
        r |= ( v == a || v == b );
        return r;
    }
    string getDescription() override{
        stringstream s;
        s << "DomRed2 rule, neigh: " << neigh << ", uv_adj: " << uv_adj;
        return s.str();
    }
};

struct DomRed3 : public LiftableRule {
    DomRed3( int vv, int uu1, int uu2, int ww ) : v(vv), u1(uu1) , u2(uu2), w(ww) {}
    int v,u1,u2,w;

    void lift(VB & res) override {
        if( res[u1] && res[u2] ) {
            res[u1] = res[u2] = false;
            res[v] = res[w] = true;
        }
    }
    string getName() override{ return "dom3"; }
    bool affectsNode(int v) override {
        return this->v == v || w == v || u1 == v || u2 == v;
    }
    string getDescription() override {
        stringstream s;
        s << "DomRed3 rule, v: " << v << ", u1: " << u1 << ", u2: " << u2 << ", w: " << w;
        return s.str();
    }
};


struct DomRedPath : public LiftableRule {
    DomRedPath( int vv, PII ww ) : v(vv), to(ww) {}
    int v;
    PII to;

    void lift(VB & res) override {
        assert(v >= 0 && v < res.size());
        assert(to.first >= 0 && to.first < res.size());
        assert(to.second >= 0 && to.second < res.size());
        if( res[v] ) {
            res[v] = false;
            auto [a,b] = to;
            if ( res[a] ) res[b] = true;
            else res[a] = true;
        }
    }
    string getName() override{ return "dom_path"; }
    bool affectsNode(int v) override { return (this->v == v) || (to.first == v) || ( to.second == v ); }
    string getDescription() override {
        stringstream s;
        s << "DomRedPath rule, v: " << v << ", swap_to: " << to;
        return s.str();
    }
};

struct PathRule : public LiftableRule {
    // explicit PathRule( VI short_pth, VI long_pth, VI vva, VI vvb ) :
    explicit PathRule( VI short_pth, VI long_pth, VI vva, VI vvb, VPII lpn ) :
        short_path(std::move(short_pth)), long_path(std::move(long_pth)), va(std::move(vva)), vb(std::move(vvb)),
        lp_neigh(std::move(lpn)) {}
    VI short_path, long_path;
    VI va, vb;
    VPII lp_neigh; // this is needed only for assertions - remove it later if path rules will work correctly
    bool is_a_hit = false, is_b_hit = false;

    void lift(VB & res) override {
        constexpr bool debug = false;
        auto & sp = short_path;
        auto & lp = long_path;

        int a = sp[0], b = sp.back();
        assert(a == lp[0]);
        assert(b == lp.back());
        assert(sp.size() <= 4);

        int n = sp.size();
        bool sp_has_res_internal_node = false;
        for( int i=1; i+1<n; i++ ) sp_has_res_internal_node |= res[sp[i]];

        bool a_hit_by_internal_node = res[ sp[1] ];
        bool b_hit_by_internal_node = res[ sp[n-2] ];

        if constexpr (debug) {
            DEBUG(is_a_hit);
            DEBUG(is_b_hit);
            DEBUG(n);
            DEBUG(sp);
            DEBUG(lp);
            for( auto v : lp ) clog << "res[" << v << "]: " << res[v] << endl;
        }
        // now clearing all internal nodes from res
        for( int i=1; i+1<sp.size(); i++ ) res[ sp[i] ] = false;

        if( (res[a] || res[b]) && ( !res[a] || !res[b] ) && (n == 3) && sp_has_res_internal_node ) {
            bool a_hit_by_external = res[a];
            for(int d : va) a_hit_by_external |= res[d];

            bool b_hit_by_external = res[b];
            for(int d : vb) b_hit_by_external |= res[d];

            if( res[a] ) {
                if constexpr (debug) clog << "Case -1" << endl;
                assert(!res[b]);
                for( int i=3; i+1 < lp.size(); i+=3 ) res[ lp[i] ] = true;
                if( !b_hit_by_external && !res[lp[lp.size()-2]] ) res[b] = true; // we must add this node as well... :(
            }else { // res[b] = true
                assert(!res[a]);
                if constexpr (debug) clog << "Case 0" << endl;
                for( int i=(int)lp.size()-4; i>=0; i-=3 ) res[ lp[i] ] = true;
                if( !a_hit_by_external && !res[lp[1]] ) res[a] = true;  // we must add this node as well... :(
            }
        }else

        if( res[a] && res[b] ) { // if both ends are hit, then we take every thord node, starting from path[2]
            if constexpr (debug) clog << "Case 1" << endl;
            for( int i=3; i+1 < lp.size(); i+=3 ) res[ lp[i] ] = true;
        }else if( res[a] ) {
            if constexpr (debug) clog << "Case 2" << endl;
            assert(!res[b]);
            // if the last internal node is in the solution, then it hits node b, hence
            for( int i=3; i<lp.size(); i+=3 ) res[ lp[i] ] = true;
        }else if( res[b] ) {
            if constexpr (debug) clog << "Case 3" << endl;
            assert(!res[a]);
            for( int i=(int)lp.size()-4; i>=0; i-=3 ) res[ lp[i] ] = true;
        }else { // neither a nor b are in the solution
            assert(!res[a] && !res[b]);

            if( sp_has_res_internal_node ) {
                if( a_hit_by_internal_node ) { // a is hit by sp[1], hence it must be in the solution...
                    if constexpr (debug) clog << "Case 4" << endl;
                    for( int i=1; i<lp.size(); i+=3 ) res[lp[i]] = true;
                }else if( b_hit_by_internal_node ) { // b is hit by sp[n-2]
                    if constexpr (debug) clog << "Case 5" << endl;
                    for( int i=(int)lp.size()-2; i>=0; i -= 3 ) res[lp[i]] = true;
                }else {
                    if constexpr (debug) clog << "Case 6" << endl;
                    for( int i=2; i<lp.size(); i+=3 ) res[lp[i]] = true;
                }
            }else {
                if constexpr (debug) clog << "Case 7" << endl;
                for( int i=2; i<lp.size(); i += 3 ) res[ lp[i] ] = true;
            }

        }

        if(true){ // just an assertion...
            bool a_hit = (res[a] || res[sp[1]] || is_a_hit );
            for(int d : va) a_hit |= res[d];

            bool b_hit = ( res[b] || res[lp[lp.size()-2]] || is_b_hit );
            for(int d : vb) b_hit |= res[d];

            if( !a_hit ) res[a] = true;
            if( !b_hit ) res[b] = true;

            // assert(a_hit);
            // assert(b_hit);
            for( int i=1; i+1<lp.size(); i++ ) {
                int v = lp[i];
                assert( res[v] || res[lp_neigh[i].first] || res[lp_neigh[i].second] );
            }
        }
    }
    string getName() override{ return "path"; }
    bool affectsNode(int v) override {
        bool r = false;
        r |= StandardUtils::find(short_path,v);
        r |= StandardUtils::find(long_path,v);
        r |= StandardUtils::find(va,v);
        r |= StandardUtils::find(vb,v);
        return r;
    }
    string getDescription() override {
        // VI short_path, long_path;
        // VI va, vb;
        // VPII lp_neigh; // this is needed only for aaesrtions - remove it later if path rules will work correctly
        // bool is_a_hit = false, is_b_hit = false;
        stringstream s;
        s << "Path rule, short_path: " << short_path << ", long_path: " << long_path << ", va: " << va
            << ", vb: " << vb << ", lp_neigh: " << lp_neigh << ", is_a_hit: " << is_a_hit << ", is_b_hit: "
            << is_b_hit;
        return s.str();
    }
};

struct FunnelFolding : public LiftableRule {
public:
    FunnelFolding(int _v, int _a, int _b, VI & _A, VI & _B) : a(_a), b(_b), v(_v), A(_A), B(_B) {}
    // ~FunnelFolding() override;

    void lift(VB& res) override {
        bool has_a = false;
        for ( int d : A ) has_a |= res[d];
        bool has_b = false;
        for ( int d : B ) has_b |= res[d];

        if (has_a) res[b] = true;
        else if ( has_b ) res[a] = true;
        else res[v] = true;
    }

    string getName() override { return "funnel_folding"; };

    bool affectsNode(int v) override {
        return a == v || this->v == v || b == v ||
            StandardUtils::find(A,v) ||
            StandardUtils::find(B,v);
    };

    string getDescription() override {
        stringstream s;
        s << "Funnel folding, v: " << v << ", a: " << a << ", b: " << b << "A: " << A << ", B: " << B;
        return s.str();
    };

private:

    int a,b,v;
    VI A,B;

};


struct Funnel2Nonfolding : public LiftableRule {
public:
    Funnel2Nonfolding(int _u, int _v, int _a, int _b, VI & _A, VI & _B, int _dom)
        : a(_a), b(_b), u(_u), v(_v), A(_A), B(_B), dom(_dom) {}

    void lift(VB& res) override {
        // if ( res[u] && res[v] ) {
        //     bool in_A = false;
        //     for (int d : A ) in_A |= res[d];
        //     bool in_B = false;
        //     for (int d : B ) in_B |= res[d];
        //
        //     if (!in_A && !in_B) {
        //         res[u] = false;
        //         res[A[0]] = true;
        //     }
        // }

        int cnt = 0;
        cnt += res[a];
        cnt += res[b];
        cnt += res[u];
        cnt += res[v];
        if (cnt >= 2) {
            res[a] = res[b] = res[u] = res[v] = false;
            if ( StandardUtils::find(A,dom) ) {
                res[dom] = res[v] = true;
                assert(!StandardUtils::find(B,dom)); // A and B must have disjoint intersections
            }
            else {
                res[dom] = res[u] = true;
                assert(StandardUtils::find(B,dom)); // dom must be in A+B, so it is in B in this case
            }
        }
    }

    string getName() override { return "funnel2_nonfolding"; };

    bool affectsNode(int v) override {
        return a == v || this->v == v || b == v || u == v ||
            StandardUtils::find(A,v) ||
            StandardUtils::find(B,v);
    };

    string getDescription() override {
        stringstream s;
        s << "Funnel2 nonfolding, u: " << u << ", v: " << v << ", a: " << a << ", b: " << b <<
            ", A: " << A << ", B: " << B;
        return s.str();
    };

private:

    int a,b,u,v, dom;
    VI A,B;

};

class DSReducer{
public:
    explicit DSReducer(VB hn = {}, VB exc = {})
           : hit_nodes(move(hn)), excluded_nodes(move(exc)){}

    tuple<VI,VB,VB,VI,vector<LiftableRule*>> reductionRulesDS(VVI & V,int time_limit_millis = 1e9,
        const bool only_basic_reductions = false);


    static void markAdditionalExcludedNodes(VVI & V, VB & hit, VB & excluded);

    int recursive_reductions_level = 0;
    bool use_recursive_reducer = false;

    /**
     * If set to true, then some lossy rules might be applied.
     * Only lossy rules that rarely produce loss will be used. Nonetheless it is unsuitable for exact track.
     */
    const bool admit_heuristic_rules = false;

    void setPermanentExcludedNodeUnhitDominator(VI penud){ permanent_excluded_node_unhit_dominator = penud; }
private:

    VB hit_nodes, excluded_nodes;
    VI permanent_excluded_node_unhit_dominator;
};

#endif //DSREDUCER_H
