//
// Created by sylwester on 3/26/22.
//

#include "datastructures/RandomSelectionSet.h"

template < typename TP >
RandomSelectionSet<TP>::RandomSelectionSet(int n) : rnd(0, 1'000'000'000ll * 1'000'000'000ll),
rnd2(0.0, 1.0){
    n++;
    N = 1;
    while( N < n ) N <<= 1;

    probab = VTP(2*N,0);
    cover = VTP(2*N,0);
    max_el = VTP(2*N,0);
    cnt_num = VI(2*N,false);
}
template RandomSelectionSet<LL>::RandomSelectionSet(int n);
template RandomSelectionSet<double>::RandomSelectionSet(int n);
template RandomSelectionSet<long double>::RandomSelectionSet(int n);


template < typename TP >
int RandomSelectionSet<TP>::getRandomElement() {
    TP max_val = max_el[1];
//    DEBUG(max_val);
    if( max_val == 0 ) return -1;
    TP r = 0;
    if constexpr ( is_integral_v<TP> ) r = rnd.nextInt(max_val);
    else r = rnd2.rand() * max_val;
    int ind = lowerBound(r);
    return ind;
}
template int RandomSelectionSet<LL>::getRandomElement();
template int RandomSelectionSet<double>::getRandomElement();
template int RandomSelectionSet<long double>::getRandomElement();

template < typename TP >
void RandomSelectionSet<TP>::set(int id, TP val) {
    if( val == 0 ){
        if( probab[id] > 0 ) {
            int x = N + id;
            while (x >= 1) {
                cnt_num[x]--;
                x = par(x);
            }
        }
    }else if( probab[id] == 0 ){
        int x = N + id;
        while( x >= 1 ){
            cnt_num[x]++;
            x = par(x);
        }
    }

    TP last_val = probab[id];
    probab[id] = val;
    TP diff = val - last_val;

    add( id, diff );
}
template void RandomSelectionSet<LL>::set(int id, LL val);
template void RandomSelectionSet<double>::set(int id, double val);
template void RandomSelectionSet<long double>::set(int id, long double val);

template < typename TP >
void RandomSelectionSet<TP>::add(int beg, TP val) {
    beg += N;
    int max_beg_ind = 2*N-1;

    while( beg > 1 ){

        int p = par(beg);
        while( beg == L(p) ){ // go up-and-right as long as possible
            beg = p;
            p = par(p);
            max_beg_ind >>= 1;
        }

//        clog << "Adding " << val << " to cover[" << beg << "]" << endl;
        cover[beg] += val;
        max_el[beg] += val;

        { // updating max_el - we need to do that only as long as we go up-and-left
            int x = beg;
            int p = par(beg);
            while( p >= 1 && x == R(p) ){
                max_el[p] = max_el[x] + cover[p];
                x = p;
                p = par(p);
//                clog << "\tmax_el[" << x << "]: " << max_el[x] << endl;
            }
        }

//        clog << "cover[" << beg << "]: " << cover[beg] << ", max_el[" << beg << "]: " << max_el[beg] << endl;
//        ENDLS(10,"*");

        if( beg < max_beg_ind ) beg++; // if we are on a rightmost slope, we cannot do anything more...
        else break;

        beg = par(beg);
        max_beg_ind >>= 1;
    }
}
template void RandomSelectionSet<LL>::add(int beg, LL val);
template void RandomSelectionSet<double>::add(int beg, double val);
template void RandomSelectionSet<long double>::add(int beg, long double val);

template < typename TP >
int RandomSelectionSet<TP>::lowerBound(TP val) {
    if( cnt_num[1] == 0 ) return -1; // all elements are 0
    if( get(N-1) < val ) return -1; // largest element is smaller than val

    int id = 1;

    while( id < N ){
        val -= cover[id];

//        DEBUG(id);
//        DEBUG(val);

        int l = L(id);
        if( cnt_num[l] > 0 && max_el[l] >= val ) id = l;
        else id = R(id);
    }

    return id - N;
}
template int RandomSelectionSet<LL>::lowerBound(LL val);
template int RandomSelectionSet<double>::lowerBound(double val);
template int RandomSelectionSet<long double>::lowerBound(long double val);

template < typename TP >
TP RandomSelectionSet<TP>::get(int id) {
    TP res = 0;
    id += N;
    while( id >= 1 ){
        res += cover[id];
        id >>= 1;
    }
    return res;
}
template LL RandomSelectionSet<LL>::get(int id);
template double RandomSelectionSet<double>::get(int id);
template long double RandomSelectionSet<long double>::get(int id);

template < typename TP >
void RandomSelectionSet<TP>::test(){

    const bool use_hand_test = false;
    if(use_hand_test){ // hand tests
        int N = 11;
        RandomSelectionSet prs(N);
        UniformIntGenerator rnd(0, 1e9);

        int T = 10;
        int U = 100;

        while (T--) {

            int ind = rnd.nextInt(N);
            int val = rnd.nextInt(U / 3);

            clog << "Setting value of ind " << ind << " to val = " << val << endl;
            prs.set(ind, val);

            clog << "Now prefix sums: " << endl;
            for (int i = 0; i < N; i++) {
                clog << "prs.get(" << i << "): " << prs.get(i) << endl;
            }

            ENDL(1);
            for (int i = 0; i < U; i += 10) {
                int lb = prs.lowerBound(i);
                clog << "prs.lowerBound(" << i << "): " << lb << endl;
                ENDL(1);
            }

            ENDL(5);
            ENDLS(50, "*");
            ENDL(5);
        }
    }

    { // automated tests
        UniformIntGenerator rnd(0, 1e9);


        int MAX_N = 300;
        for( int i=1; i<=MAX_N; i++ ){
            clog << "\rRandomSelectionSet test progress: " << i << " / " << MAX_N << flush;

            int N = i;
            int U = 1e9;

            VLL vals(N);
            VLL ps(N);
            RandomSelectionSet prs(N);

            for( int j=0; j<10*N; j++ ){

                int ind = rnd.nextInt(N);
                int val = rnd.nextInt(U/3);
                prs.set( ind, val );

                int ind2 = rnd.nextInt(N);
                prs.set(ind2,0);

                // updating brute force
                vals[ind] = val;
                vals[ind2] = 0;
                ps[0] = vals[0];
                for(int r=1; r<N; r++) ps[r] = ps[r-1] + vals[r];

                auto write = [&](int psv, int v, int brute_ind, int prs_ind){
                    DEBUG(vals);
                    DEBUG(ps);
                    DEBUG(psv);
                    DEBUG(v);
                    DEBUG(brute_ind);
                    DEBUG(prs_ind);
                };

                for( int r=0; r<N; r++ ){
                    if( prs.get(r) != ps[r] ){
                        DEBUG(vals);
                        DEBUG(ps);
                        DEBUG(r);
                        DEBUG(ps[r]);
                        DEBUG(prs.get(r));
                        assert(prs.get(r) == ps[r]);
                    }

                    {
                        int v = ps[r] - 1;
                        v = max(v,1);

                        auto it = lower_bound(ALL(ps), v);
                        int brute_ind = it - ps.begin();
                        if(brute_ind == N) brute_ind = -1;

                        int prs_ind = prs.lowerBound(v);

                        if(brute_ind != prs_ind){
                            write(ps[r], v, brute_ind, prs_ind);
                            assert( brute_ind == prs_ind );
                        }
                    }

                    {
                        int v = ps[r];
                        v = max(v,1);

                        auto it = lower_bound(ALL(ps), v);
                        int brute_ind = it - ps.begin();
                        if(brute_ind == N) brute_ind = -1;

                        int prs_ind = prs.lowerBound(v);

                        if(brute_ind != prs_ind){
                            write(ps[r], v, brute_ind, prs_ind);
                            assert( brute_ind == prs_ind );
                        }
                    }

                    {
                        int v = ps[r]+1;
                        v = max(v,1);

                        auto it = lower_bound(ALL(ps), v);
                        int brute_ind = it - ps.begin();
                        if(brute_ind == N) brute_ind = -1;

                        int prs_ind = prs.lowerBound(v);

                        if(brute_ind != prs_ind){
                            write(ps[r], v, brute_ind, prs_ind);
                            assert( brute_ind == prs_ind );
                        }
                    }

                }
            }
        }
    }
}

