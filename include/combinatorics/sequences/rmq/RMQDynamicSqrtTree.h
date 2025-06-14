//
// Created by sylwester on 9/19/19.
//

#ifndef ALGORITHMSPROJECT_RMQDYNAMICSQRTTREE_H
#define ALGORITHMSPROJECT_RMQDYNAMICSQRTTREE_H

#include "datastructures/SqrtTree.h"
#include "Constants.h"

/**
 * RMQ using SqrtTree. Preprocessing done in O(N * loglogN). Queries in O(1). Updating SINGLE elements only and done in O(sqrt(N)).
 * @tparam _T
 */
template<class _T>
class RMQDynamicSqrtTree{
public:
    typedef vector<_T> VT;
    RMQDynamicSqrtTree( VT tab ) : tree ( SqrtTree<MinSqrtItem>( vector<MinSqrtItem>() ) ) {
        vector<MinSqrtItem> items;
        for(int i=0; i<tab.size(); i++) items.emplace_back( tab[i],i );
        tree = SqrtTree<MinSqrtItem>(items);
    }

    /**
     *
     * @param a
     * @param b
     * @return index of the minimum on given interval
     */
    int query( int a, int b ){
        return tree.query(a,b).ind;
    }

    /**
     * updates element at position ind to given value.
     * @param ind
     * @param value
     */
    void update( int ind, _T value ){
        tree.update( ind, MinSqrtItem(value,ind) );
    }


    static void test(){
        int l_zest = 50;

        while(l_zest--){

            int N = 1e4;
            VI tab;
            for(int i=0; i<N; i++) tab.push_back( rand()% (int)1e2 );


            {
                RMQDynamicSqrtTree<int> rmq(tab);


                for (int i = 0; i < N; i++) {
                    for (int k = i; k < min(N, i + (int) sqrt(N)); k++) {
                        //            for( int k=i; k<N; k++ ){

                        int m1 = tab[rmq.query(i, k)];

                        int m2 = *min_element(tab.begin() + i, tab.begin() + k + 1);

                        if (m1 != m2) {
                            cout << "m1 = " << m1 << "    !=    m2 = " << m2 << endl;
                            exit(1);
                        }
                    }
                }

            }
        }



        cout << "PASSED" << endl;

    }

private:

    struct MinSqrtItem{
        MinSqrtItem(_T m = Constants::INF, int ind = -1){
            this->m = m;
            this->ind = ind;
        }
        static MinSqrtItem op( MinSqrtItem & a, MinSqrtItem & b ){
            if( a.m < b.m ) return MinSqrtItem( a.m,a.ind );
            else return MinSqrtItem(b.m,b.ind);
        }

        _T m;
        int ind;
    };

    SqrtTree<MinSqrtItem> tree;
};

#endif //ALGORITHMSPROJECT_RMQDYNAMICSQRTTREE_H
