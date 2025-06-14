//
// Created by sylwester on 11/4/22.
//

#include <utils/StandardUtils.h>
#include "combinatorics/sequences/IntegerSequenceCreator.h"


template<class _T>
vector<_T> IntegerSequenceCreator::getRandom(_T U, _T N) {
    vector<_T> res(N);
    UniformIntGenerator rnd(0,U);
    for(auto & d : res) d = rnd.rand();
    return res;
}
template VI IntegerSequenceCreator::getRandom<int>(int U, int N);
template VLL IntegerSequenceCreator::getRandom<LL>(LL U, LL N);





template<class _T>
vector<_T> IntegerSequenceCreator::getRandom(_T L, _T R, _T N) {
    auto seq = getRandom(R - L, N);
    for(auto & d : seq) d += L;
    return seq;
}
template VI IntegerSequenceCreator::getRandom<int>(int L, int R, int N);
template VLL IntegerSequenceCreator::getRandom<LL>(LL L, LL R, LL N);






template<class _T>
vector<_T> IntegerSequenceCreator::getSquareFree(_T L, _T R, _T N) {
    _T D = R-L+1;
    VB is_sqfree(D,true);
    for( _T p = 2; p*p <= R; p += ( (p==2) ? 1 : 2 ) ){
        _T p2 = p*p;
        _T t = L * _T((p2+L-1)/L);
        assert( t >= L && t-p2 < L );
        while( t <= R ){
            is_sqfree[t-L] = false;
            t += p2;
        }
    }

    UniformIntGenerator rnd(0, 1'000'000'000ll * 1'000'000'000);
    set<pair<LL,_T>> zb;

    for( _T i=0; i<D; i++ ){
        if( is_sqfree[i] ){
            zb.insert( {rnd.rand(),i+L} ); // only those with largest randomly generated hash will be kept
            if(zb.size() > N) zb.erase(zb.begin());
        }
    }

    vector<_T> res;
    res.reserve(zb.size());
    for( auto & p : zb ) res.push_back(p.second);

    return res;
}
template VI IntegerSequenceCreator::getSquareFree<int>(int L, int R, int N);
template VLL IntegerSequenceCreator::getSquareFree<LL>(LL L, LL R, LL N);





template<class _T>
vector<_T> IntegerSequenceCreator::getSquares(_T L, _T R, _T N) {
    UniformIntGenerator rnd(0, 1'000'000'000ll * 1'000'000'000);
    set<pair<LL,_T>> zb;

    for( _T i = sqrt(L); i*i <= R; i++ ){
        if( i*i >= L ){
            zb.insert( {rnd.rand(),i*i} );
            if(zb.size() > N) zb.erase(zb.begin());
        }
    }

    vector<_T> res;
    res.reserve(zb.size());
    for( auto & p : zb ) res.push_back(p.second);

    return res;
}
template VI IntegerSequenceCreator::getSquares<int>(int L, int R, int N);
template VLL IntegerSequenceCreator::getSquares<LL>(LL L, LL R, LL N);




template<class _T>
vector<_T> IntegerSequenceCreator::getRandomSequenceWithGivenSum(_T N, _T S, _T U) {
    LL S0 = S;

    UniformIntGenerator rnd(0,max((LL)S, 1'000'000'000ll * 1'000'000ll));
    vector<_T> seq(N);

    U = min(U,S);
    for( int i=0; i<N; i++ ){
        if( S <= 0 || U < 0){
            seq[i] = 0;
            continue;
        }
        LL val = rnd.nextInt(U+1);
        seq[i] = val;
        S -= val;
        if( S < U ) U = S;
    }

    StandardUtils::shuffle(seq);
    S = S0 - accumulate(ALL(seq),0);
    assert(S >= 0);

    // to ensure that we have sum equal S0, we know maximize those elements that are < U to value U
    if( S > 0 ){
        for( auto & d : seq ){
            if( S > 0 ){
                LL diff = min( S, U-d );
                S -= diff;
                d += diff;
            }
        }
    }

    StandardUtils::shuffle(seq);
    assert( accumulate(ALL(seq),0) == S0 );

    assert(seq.size() == N);

    return seq;
}
template VI IntegerSequenceCreator::getRandomSequenceWithGivenSum<int>(int N, int S, int U);
template VLL IntegerSequenceCreator::getRandomSequenceWithGivenSum<LL>(LL N, LL S, LL U);


// **************************************************************    TRANSFORMATIONS






template<class _T>
vector<_T> IntegerSequenceCreator::cyclicFill(vector<_T> seq, _T N) {
    vector<_T> res(N);
    for( int i=0; i<N; i++ ) res[i] = seq[i%seq.size()];
    return res;
}
template VI IntegerSequenceCreator::cyclicFill<int>(VI seq, int N);
template VLL IntegerSequenceCreator::cyclicFill<LL>(VLL seq, LL N);


template<class _T>
vector<_T> IntegerSequenceCreator::sortOnIntervals(vector<_T> seq, pair<_T,_T> lbnd) {
    UniformIntGenerator rnd(lbnd.first, lbnd.second);
    int p = 0;
    while( p < seq.size() ){
        int q = p + rnd.rand();
        q = min(q,(int)seq.size());
        sort( seq.begin()+p, seq.begin()+q );
        p = q;
    }
    return seq;
}
template VI IntegerSequenceCreator::sortOnIntervals<int>(VI  seq, PII lbnd);
template VLL IntegerSequenceCreator::sortOnIntervals<LL>(VLL seq, PLL lbnd);



template<class _T>
vector<_T> IntegerSequenceCreator::shuffleOnIntervals(vector<_T> seq, pair<_T, _T> lbnd) {
    UniformIntGenerator rnd(lbnd.first, lbnd.second);
    int p = 0;
    while( p < seq.size() ){
        int q = p + rnd.rand();
        q = min(q,(int)seq.size());
        shuffle( seq.begin()+p, seq.begin()+q, rnd.getRNG() );
        p = q;
    }
    return seq;
}
template VI IntegerSequenceCreator::shuffleOnIntervals<int>(VI  seq, PII lbnd);
template VLL IntegerSequenceCreator::shuffleOnIntervals<LL>(VLL seq, PLL lbnd);



template<class _T>
vector<_T> IntegerSequenceCreator::hillsAndValleys(vector<_T> seq, pair<_T, _T> lbnd) {
    UniformIntGenerator rnd(lbnd.first, lbnd.second);
    int p = 0;
    int cnt = 0;
    while( p < seq.size() ){
        int q = p + rnd.rand();
        q = min(q,(int)seq.size());
        if( (cnt++ & 1) == 0 ) sort( seq.begin()+p, seq.begin()+q );
        p = q;
    }
    return seq;
}
template VI IntegerSequenceCreator::hillsAndValleys<int>(VI  seq, PII lbnd);
template VLL IntegerSequenceCreator::hillsAndValleys<LL>(VLL seq, PLL lbnd);



template<class _T>
vector<_T> IntegerSequenceCreator::reflect(vector<_T> seq, _T U) {
    for( auto & d : seq ) d = U - d;
    return seq;
}
template VI IntegerSequenceCreator::reflect<int>(VI seq, int U);
template VLL IntegerSequenceCreator::reflect<LL>(VLL seq, LL U);



template<class _T>
vector<_T> IntegerSequenceCreator::add(vector<_T> seq, _T a) {
    for( auto & d : seq ) d += a;
    return seq;
}
template VI IntegerSequenceCreator::add<int>(VI seq, int a);
template VLL IntegerSequenceCreator::add<LL>(VLL seq, LL a);



template<class _T>
vector<_T> IntegerSequenceCreator::multiply(vector<_T> seq, _T a) {
    for( auto & d : seq ) d *= a;
    return seq;
}
template VI IntegerSequenceCreator::multiply<int>(VI seq, int a);
template VLL IntegerSequenceCreator::multiply<LL>(VLL seq, LL a);


template<class _T>
vector<_T> IntegerSequenceCreator::modulate(vector<_T> seq, _T a) {
    for( auto & d : seq ) d %= a;
    return seq;
}
template VI IntegerSequenceCreator::modulate<int>(VI seq, int a);
template VLL IntegerSequenceCreator::modulate<LL>(VLL seq, LL a);

template<class _T>
vector<_T> IntegerSequenceCreator::concentric(vector<_T> seq) {
    seq = reflect<_T>(seq,0);
    excentric(seq);
    seq = reflect<_T>(seq,0);
    return seq;
}
template VI IntegerSequenceCreator::concentric<int>(VI seq);
template VLL IntegerSequenceCreator::concentric<LL>(VLL seq);



template<class _T>
vector<_T> IntegerSequenceCreator::excentric(vector<_T> seq) {
    sort(ALL(seq));
    reverse(ALL(seq));
    auto res = seq;
    int N = seq.size();

    for( int i=0; i<N/2; i++ ){
        res[i] = seq[2*i];
        res[N-1-i] = seq[2*i+1];
    }

    swap(seq,res);
    return res;
}
template VI IntegerSequenceCreator::excentric<int>(VI seq);
template VLL IntegerSequenceCreator::excentric<LL>(VLL seq);





template<class _T>
vector<vector<_T>>
IntegerSequenceCreator::getRandomWithGuaranteedLongestCommonSubstring(_T N, _T U, _T L, _T guarantee, _T char_cnt) {
    auto pattern = getRandom(U,L);
    vector<vector<_T>> res(N);

    UniformIntGenerator rnd1(0,U);
    UniformIntGenerator rnd2(0,L-guarantee-1);

    for( int i=0; i<N; i++ ){
        res[i] = pattern;
        for( int j=0; j<char_cnt; j++ ) res[i][ rnd2.rand() ] = rnd1.rand();
        rotate( res[i].begin(), res[i].begin() + rnd2.rand(), res[i].end() );
    }

    return res;
}
template VVI IntegerSequenceCreator::getRandomWithGuaranteedLongestCommonSubstring<int>(int N, int U, int L,
        int guarantee, int char_cnt);
template VVLL IntegerSequenceCreator::getRandomWithGuaranteedLongestCommonSubstring<LL>(LL N, LL U, LL L,
                                                                                      LL guarantee, LL char_cnt);



template<class _T>
vector<_T> IntegerSequenceCreator::range(_T a, _T b, _T step) {
    vector<_T> res;
    res.reserve( 1 + (b-a+step-1)/step );
    while( a <= b ){
        res.push_back(a);
        a += step;
    }
    return res;
}
template VI IntegerSequenceCreator::range(int a, int b, int step);
template VLL IntegerSequenceCreator::range(LL a, LL b, LL step);



