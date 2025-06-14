//
// Created by sylwester on 8/8/19.
//

#include <graphs/VertexCover/VCUtils.h>
#include <graphs/VertexCover/approximation/LibMVC/fastvc.h>

VI VCUtils::getRandomPermutation( int N ){
    VI perm(N);
    iota(ALL(perm),0);
    random_shuffle(ALL(perm));
    return perm;
}

VI VCUtils::fillRandomToMinimalVC( VVI V, VI vc ){
    vector<bool> inVC( V.size(),false );
    for(auto p : vc) inVC[p] = true;

    VI perm = getRandomPermutation( V.size() );
    for( int p : perm ){
        if( inVC[p] ) continue;

        for( int d : V[p] ){
            if( !inVC[d] ){
                inVC[d] = true;
                vc.push_back(d);
            }
        }
    }

    return vc;
}


VI VCUtils::getRandomMinimalVC( VVI & V ){
    VI vc;
    return fillRandomToMinimalVC( V, vc );
}

VI VCUtils::getRandomMIS( VVI & V ){
    VI mis;
    return fillRandomToMaximalIS( V,mis );
}

VI VCUtils::fillRandomToMaximalIS( VVI & V, VI mis ){
    VI perm = getRandomPermutation( V.size() );
    mis = fillRandomToMaximalIS( V, perm, mis );

    return mis;
}

VI VCUtils::fillRandomToMaximalIS(VVI &V, VI fillFrom, VI mis) {

    VB inMis(V.size(),false);
    for(int p : mis) inMis[p] = true;

    random_shuffle(ALL(fillFrom));
    for( int p : fillFrom ){
        if( inMis[p] ) continue;
        bool hasNeighborInMis = false;
        for( int d : V[p] ){
            if( inMis[d] ){
                hasNeighborInMis = true;
                break;
            }
        }

        if( !hasNeighborInMis ){
            inMis[p] = true;
            mis.push_back(p);
        }
    }


    return mis;
}

bool VCUtils::isVertexCover( VVI & V, VI & vc ){
    VB inVC(V.size(),false);
    for(int p : vc) inVC[p] = true;
    for( int i=0; i<V.size(); i++ ){
        if(inVC[i]) continue;
        for(int d : V[i]){
            if( !inVC[d] ) return false;
        }
    }
    return true;
}

VI VCUtils::getVCGreedyMaxDegree(VVI &V) {
    VI perm(V.size());
    iota(ALL(perm),0);

    sort( ALL(perm), [&perm, &V]( int a, int b ){ return V[a].size() > V[b].size(); } );
    VB inVC(V.size(),false);
    VI res;
    for( int i=0; i<perm.size(); i++ ){
        int d = perm[i];
        bool addToVC = false;
        for( int p : V[d] ){
            if( !inVC[p] ){
                addToVC = true;
                break;
            }
        }

        if( addToVC ){
            res.push_back(d);
            inVC[d] = true;
        }
    }
    return res;
}


bool VCUtils::isIndependentSet(VVI &V, VI &S) {
    VI perm(V.size());
    iota(ALL(perm),0);
    VI S2 = S;
    sort(ALL(S2));
    VI vc;
    set_difference( ALL(perm), ALL(S2),  std::back_inserter(vc) );
    bool res = isVertexCover( V,vc );
    return res;
}


bool VCUtils::isMaximalIndependentSet(VVI &V, VI &mis) {
    VB was(V.size(),false);
    for( int d : mis ){
        was[d] = true;
        for(int p : V[d]) was[p] = true;
    }

    for( int i=0; i<V.size(); i++ ){
        if( !was[i] ){
            return false;
        }
    }
    return true;
}



