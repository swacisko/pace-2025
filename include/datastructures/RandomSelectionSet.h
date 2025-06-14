//
// Created by sylwester on 3/26/22.
//

#ifndef ALGORITHMSPROJECT_RANDOMSELECTIONSET_H
#define ALGORITHMSPROJECT_RANDOMSELECTIONSET_H

#include <utils/RandomNumberGenerators.h>
#include "Makros.h"

/**
 * This is a class that represents a probability set. IT can be used to efficiently solve the following problem:
 * You are given N elements, each has its value. Choose 1 of them with probability proportional to some function of
 * its value val(i). Change value of some element.
 *
 * This structure allows O(logN) time query for random element and O(logN) update of a value.
 * It it implemented as a segment tree that stores prefix sums - that is, when some value is set to i-th element,
 * we add interval [i,N] with that value. It also allows lower bounding that can be used to find an element for
 * given random integer from range [0, last_element_prefsuf_value).
 */
template<typename TP>
class RandomSelectionSet{
public:

    using VTP = vector<TP>;

    RandomSelectionSet(int N );

    /**
     * Finds and returns id of the element chosen randomly with probability proportional to the value in [probab]
     */
    int getRandomElement();

    /**
     * Sets value of id-th element to given value.
     */
    void set( int id, TP val );

    /**
     * Finds an returns smallest INDEX of an element with prefix sum >= val
     */
    int lowerBound( TP val );

    /**
    * Find and return value of prefix sum on given position id.
    */
    TP get( int id );

    /**
     * Get the relative probability of selecting node id.
     */
    TP getProbab(int id){ return probab[id]; }

    static void test();

private:

    // smallest power of two not smaller than the maximum number of elements
    int N;
    UniformIntGenerator rnd;
    UniformDoubleGenerator rnd2;

    // probability of choosing i-th element is equal to probab[i] / sum(probab)
    VTP probab;

    /**
     * Table total sum of intervals covering given interval - usual for segment tree.
     */
    VTP cover;

    /**
     * cnt_num[i] is the number of nonzero elements in interval represented by node i.
     * This is used to correctly treat lowerBound
     */
    VI cnt_num;

    /**
     * max_el[i] is the maximum value of an element that can be reached from this node. It is always the rightmost
     * element of the interval represented bu node i, because we keep prefix sums, so the sequence is nondecreasing.
     * This array DOES include the value of cover of given node.
     */
    VTP max_el;


    /**
     * Adds given value [val] to all elements in the interval [beg,N)
     */
    void add( int id, TP val );

    int L(int x){ return x<<1; }
    int R(int x){ return (x<<1)+1; }
    int par(int x){ return x >> 1; }

};

#endif //ALGORITHMSPROJECT_RANDOMSELECTIONSET_H
