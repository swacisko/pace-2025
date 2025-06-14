//
// Created by sylwester on 8/27/19.
//

#ifndef ALGORITHMSPROJECT_COMBINATORICUTILS_H
#define ALGORITHMSPROJECT_COMBINATORICUTILS_H

#include <utils/RandomNumberGenerators.h>
#include "Makros.h"

namespace CombinatoricUtils{

    /**
     *
     * @param N size of permutation
     * @return random permutation of {0, ... ,N-1}
     */
    extern VI getRandomPermutation( int N );

    extern VI getRandomPermutation( int N, unsigned seed );

    /**
     * @return set difference {0, ... , N-1} \ A
     */
    extern VI getFullSetDifference( int N, VI  A );

    /**
     * @return random N-element sequence with elements from universe {0, ... , U}
     */
    extern VI getRandomSequence( int U, int N );
    extern VI getRandomSequence( int U, int N, unsigned seed );

    /**
     * @return random subset of elements from universe {0,...,U}
     */
    extern VI getRandomSubset( int U, int L );
    extern VLL getRandomSubset( LL U, LL L, unsigned seed = 1 );

    /**
     * @return random subset of elements from universe {0,...,U}, using specified seed
     */
    extern VI getRandomSubset( int U, int L, unsigned seed );
    extern VLL getRandomSubset( LL U, LL L, unsigned seed );

    /**
     * Creates a random sequence with N elements, where each element is selected randomly from range [0,U],
     * and whose total sum equals S.
     * Sequence is created greedily, so if the values N,S,U are not selected properly, then the sequence may be
     * far from 'uniform profile'.
     * It must hold N*U >= S to be able to create such a sequence. If not, then empty vector is returned.
     */
    extern VLL getRandomSequenceWithGivenSum( int N, LL S, LL U );

    /**
     *
     * @tparam _T
     * @param universe
     * @param L
     * @return random sequence of length @{L} with elemenents from given @{universe}
     */
    template<class _T>
    vector<_T> getRandomSequence( vector<_T> & universe, int L ){
        UniformIntGenerator gen(0,universe.size()-1);
        vector<_T> res;
        res.reserve( L );
        for( int i=0; i<L; i++ ) res.push_back( universe[ gen.rand() ] );
        return res;
    }




    /**
     * Function iterates over all partitions of the form (A_1, A_2, ... , A_t) where t is the size of @{sets} - it will be 0 <= A_i < sets[i].
     * Whenever an element d from set at index ind is added or removed to currently created sequence, we call function fun(seq, ind, s, added), where added is true,
     * if an elements was added and false if it was removed, and s is the index of element hosen from A[ind]. This enables us to quickly update
     * data. (e.g. when we calculate all possible products, we modif current product after an element is added or removed).
     * @param sets
     * @param fun
     */
    void allPartitions( VI & sets, function< void( VI&, int ind, int d, bool added ) > fun );


    /**
     * Calculates and returns number of integers from range [L,R], that have [bit]-th bit set to 1.
     * Works in O(logU) time.
     */
    LL countNumbersFromIntervalWithSetBit(LL L, LL R, int bit );
}


#endif //ALGORITHMSPROJECT_COMBINATORICUTILS_H
