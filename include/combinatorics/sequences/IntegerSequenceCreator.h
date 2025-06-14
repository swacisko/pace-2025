//
// Created by sylwester on 11/4/22.
//

#ifndef ALGORITHMSPROJECT_INTEGERSEQUENCECREATOR_H
#define ALGORITHMSPROJECT_INTEGERSEQUENCECREATOR_H

#include "Makros.h"
#include "combinatorics/CombinatoricUtils.h"

class IntegerSequenceCreator{
public:

    enum IntegerSequenceType{
        random, // random from some range [L,R]
        random_multiplied, // selected random from some range [L,R] then multiplied all by some int d
        primes, // only primes from some range [L,R]
        primes_two, // only integers that are of the form pq, where p and q are primes, from some range [L,R]
        squares, // only squares of integers, from some range [L,R]
        square_free, // only integers that are square free (product of distinct primes) , from some range [L,R]
        divisors_lot, // integers with a lot of divisors
        cyclic, // a sequence of some length T will be repeated roughly N/T times (321 321 32)
        hills_and_valleys, // consecutive segments of increasing/decreasing numbers (123 654)
        segments_reversed // sequence divided into blocks, then each block is sorted in non-ascending order (321 654)
    };


    /**
     * Creates and returns a random N-element sequence of integers from range [0,U].
     * Works int O(N) time.
     */
    template<class _T>
    static vector<_T> getRandom(_T U, _T N );


    /**
     * Creates and returns a random N-element sequence of integers from range [L,R]
     * Works nt O(N) time.
     */
    template<class _T>
    static vector<_T> getRandom(_T L, _T R, _T N );


    /**
     * Creates and returns a sequence with all at most N randomly selected square-free integers from range [L,R].
     * If the interval [L,R] contains less than N square-free integers, then all are returned.
     *
     * Works in O( (R-L) + sqrt(R) + N ) time and O(N + (R-L)/32 ) memory
     *
     * Selected integers are returned in random order.
     */
    template<class _T>
    static vector<_T> getSquareFree( _T L, _T R, _T N );


    /**
     * Creates and returns N elements from range [L,R] that have greatest number of divisors.
     * If two elements have the same number of divisors, then the larger one is considered before the smaller one.
     *
     * Works in time O( (R-L)* (sqrt(R)+logN) N ) and O(N + sqrt(R)) memory (creates a list of primes up to sqrt(R)).
     *
     * First for each integer from range factorizes it brutally and finds the number of divisors.
     * Then stores in a set only N number with greatest number of divisors
     */
    template<class _T>
    static vector<_T> getDivisorsLot( _T L, _T R, _T N );


    /**
     * Creates and returns at most N randomly selected prime integers from range [L,R].
     * If there are less than N primes in the interval, all are returned.
     * Primality os checked using Miller-Rabin test, so the total time complexity is
     */
    template<class _T>
    static vector<_T> getPrimes( _T L, _T R, _T N );

    /**
     * Creates and returns at most N randomly selected squares from range [L,R].
     * If there are less than N squares in the interval, all are returned.
     * Works in time O(sqrt(R))
     */
    template<class _T>
    static vector<_T> getSquares( _T L, _T R, _T N );

    /**
     * Creates a random sequence with N elements, where each element is selected randomly from range [0,U],
     * and whose total sum equals S.
     * Sequence is created greedily, so if the values N,S,U are not selected properly, then the sequence may be
     * far from 'uniform profile'.
     */
    template<class _T>
    static vector<_T> getRandomSequenceWithGivenSum( _T N, _T S, _T U );

    /**
     * Creates a set of [N] 'strings' (arrays with integers), each of length [L] and elements from universe [U].
     * All [N] string will have longest common substring of length at least [guarantee].
     * Sequence is created as follows:
     * First a 'pattern' sequence is created as a random sequence of length [L] over universe [U].
     * Then each of [N] sequences is created as a copy of the pattern, then [char_cnt] characters from random positions
     * from range [0 : L-guarantee-1] are selected and changed to random value from [U].
     * At the end the string is rotated by some random value from range [0 : L-guarantee-1]
     */
    template<class _T>
    static vector<vector<_T>> getRandomWithGuaranteedLongestCommonSubstring( _T N, _T U, _T L, _T guarantee, _T char_cnt );


    /**
     * 'Equivalent' of pythons range function.
     * Values [a], [b] must be nonnegative and a <= b, [step] must be positive.
     * Values a, a+step, a+2*step, ..., are generated.
     * CAUTION!
     * Maximal possibly value to generate is b (in python it would be b-1)
     */
    template<class _T>
    static vector<_T> range( _T a, _T b, _T step );

    //**********************************   TRANSFORMATIONS

    /**
     * Creates a sequence res of length N in which res[i] = seq[i%seq.size()]
     */
    template<class _T>
    static vector<_T> cyclicFill(vector<_T> seq, _T N );


    /**
     * Greedily chooses a random number from [lbnd.first, lbnd.second], then sorts consecutive interval of that length.
     */
    template<class _T>
    static vector<_T> sortOnIntervals( vector<_T> seq, pair<_T,_T> lbnd );

    /**
     * Greedily chooses a random number from [lbnd.first, lbnd.second], then shuffles elements in consecutive intervals
     * of that length.
     */
    template<class _T>
    static vector<_T> shuffleOnIntervals( vector<_T> seq, pair<_T,_T> lbnd );

    /**
     * Greedily chooses a random number from [lbnd.first, lbnd.second], then
     * sorts every second consecutive interval of that length, starting from the first one.
     */
    template<class _T>
    static vector<_T> hillsAndValleys( vector<_T> seq, pair<_T,_T> lbnd );

    /**
     * For each integer in the sequence applies transformation  x -> U - x
     */
    template<class _T>
    static vector<_T> reflect( vector<_T> seq, _T U );

    /**
     * For each integer in the sequence applies transformation  x -> x + a
     */
    template<class _T>
    static vector<_T> add( vector<_T> seq, _T a );

    /**
     * For each integer in the sequence applies transformation  x -> x * a
     */
    template<class _T>
    static vector<_T> multiply( vector<_T> seq, _T a );

    /**
     * For each integer in the sequence applies transformation  x -> x % a
     */
    template<class _T>
    static vector<_T> modulate( vector<_T> seq, _T a );

    /**
     * Makes the sequence concentric, that is of the form
     * 0 2 4 ...    5 3 1, where numbers here simply denote elements in their sorted order
     */
    template<class _T>
    static vector<_T> concentric( vector<_T> seq );

    /**
     * Makes the sequence excentric, that is of the form
     * N (N-2) ... (N-3) (N-1), where numbers here simply denote elements in their sorted order
     */
    template<class _T>
    static vector<_T> excentric( vector<_T> seq);








    static void test();
};


#endif //ALGORITHMSPROJECT_INTEGERSEQUENCECREATOR_H
