//
// Created by sylwester on 3/17/21.
//

#include "graphs/GraphTrimmer.h"
#include "CollectionOperators.h"

//#include "gtest/gtest.h"

GraphTrimmer::GraphTrimmer(VVI &V) {
    this->V = &V;
    N = V.size();
    was = VB(N,false);
}

VVI GraphTrimmer::findMaximalPathsAndCycles() {
    VVI res;
    fill(ALL(was),false);

    for( int i=0; i<N; i++ ){
        if( (*V)[i].size() == 0 ) continue;

        if( !was[i] && (*V)[i].size() <= 2 ){
            VI pth = getPathWithNode(i);
            res.push_back(pth);
        }
    }
    return res;
}

void GraphTrimmer::addToPath(int num, VI &path, VB &was) {
    assert( (*V)[num].size() <= 2 );
    path.push_back(num);
    was[num] = true;

    for( int d : (*V)[num] ){
        if( !was[d] && (*V)[d].size() <= 2 ) addToPath( d, path,was );
    }
}

VI GraphTrimmer::getPathWithNode(int num) {
    VVI pth(2);
    was[num] = true;

    for( int i=0; i<(*V)[num].size(); i++ ){
        int d = (*V)[num][i];
        if( !was[d] && (*V)[d].size() <= 2 ) addToPath( d,pth[i],was );
    }

    VI res = (-pth[0]) + VI(1,num) + pth[1];
    if( (*V)[res.back()].size() == 1 ) res = -res;

    return res;
}

