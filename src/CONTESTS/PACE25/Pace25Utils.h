//
// Created by sylwe on 04/03/2025.
//

#ifndef PACE25UTILS_H
#define PACE25UTILS_H

#include <atomic>
#include <chrono>
#include <csignal>
#include <RandomNumberGenerators.h>

#include "Makros.h"

enum HSMethod {
    MILP = 0,
    FINDMINHS = 1,
    NONE = 2,
    SAT = 3,
    CPSAT = 4,
    ILPOR = 5,
};

constexpr int inf = 1e9;

class IntGenerator {
    using AULL = atomic<ULL>;

    ULL x,y,z;
    // static AULL xx,yy,zz;
    static atomic<ULL> last_seed;
    // static volatile AULL xx,yy,zz;



public:

    static constexpr int K = 10'000;
    using seed_type = tuple<ULL,ULL,ULL>;
    static constexpr array<seed_type,K> createSeedSets() {
        ULL x=123456789, y=362436069, z=521288629;
        array<seed_type,K> seed_sets;

        for ( int i=0; i<K; i++ ) {
            seed_sets[i] = {x,y,z};
            int r = 100;
            while (r--) {
                ULL t;

                x ^= x << 16;
                x ^= x >> 5;
                x ^= x << 1;

                t = x;
                x = y;
                y = z;
                z = t ^ x ^ y;
            }
        }
        for ( int i=0; i<K; i++ ) {
            x ^= x << 16; x ^= x >> 5; x ^= x << 1;
            ULL t = x; x = y; y = z; z = t ^ x ^ y;
            swap( seed_sets[K-1-i], seed_sets[t % (K-i)] );
        }
        return seed_sets;
    }
    static array<seed_type,K> seed_sets; // = createSeedSets();

    IntGenerator(ULL seed = -1) {
        if( seed == -1 ) seed = last_seed++;

        tie(x,y,z) = seed_sets[seed % K];
        for (int i=0; i<(seed%17); i++) shiftSeed();

        constexpr bool use_slight_shifting = false;
        int x_shift, y_shift, z_shift;
        if constexpr (use_slight_shifting) {
            x_shift = (seed & 7);
            y_shift = ((seed >> 3) & 7);
            z_shift = ((seed >> 6) & 7);
        }
        // tie(x,y,z) = seed_sets[seed % K];
        if constexpr (use_slight_shifting) {
            x += -3 + x_shift;
            y += -3 + y_shift;
            z += -3 + z_shift;
        }
    }


    // IntGenerator() {
    // // IntGenerator() : rnd(0, ULLONG_MAX,(int)zz) {
    //     x = xx;
    //     y = yy;
    //     z = zz;
    //     // if( (z % 10) == 0 )
    //     for( int i=0; i<1+(z%10); i++ )
    //         shiftSeed();
    // }

    // ~IntGenerator() {
    //     xx = x;
    //     yy = y;
    //     zz = z;
    // }

    unsigned long long xorshf96() {          //period 2^96-1
        ULL t;

        x ^= x << 16;
        x ^= x >> 5;
        x ^= x << 1;

        t = x;
        x = y;
        y = z;
        z = t ^ x ^ y;

        return z;
    }


    ULL nextInt(const ULL N){ return xorshf96() % N; }
    ULL rand(){ return xorshf96(); }

    // ULL nextInt(int N){ return rnd.nextInt(N); }
    // ULL rand(){ return rnd.rand(); }
    // UniformIntGenerator rnd;

private:
    void shiftSeed() {          //period 2^96-1
        x ^= x << 16; x ^= x >> 5; x ^= x << 1;
        ULL t = 0 ^ x; x = 0 ^ y; y = 0 ^ z; z = t ^ x ^ y;
    }
};


class BloomFilter {
public:

    /**
     * Creates a bloom filter with N bits. Please note, that the number of bits should usually be 32/64 times the number of
     * elements inserted.
     */
    explicit BloomFilter(const ULL N ) : was(bit_ceil(N),false), SZ( bit_ceil(N)) {}

    void insert(const ULL h) { add(h); }
    void insertHalf(const ULL h) { addHalf(h); }

    static constexpr bool use_large_set = true;
    void add(const ULL val) {
        was[hash1(val)] = true;
        was[hash2(val)] = true;
        was[hash3(val)] = true;
        was[hash4(val)] = true;
        was[hash5(val)] = true;
        if constexpr (use_large_set) {
            was[hash6(val)] = true;
            was[hash7(val)] = true;
            was[hash8(val)] = true;
            was[hash9(val)] = true;
            was[hash10(val)] = true;
        }
    }
    void addHalf(const ULL val) {
        was[hash1(val)] = true;
        was[hash2(val)] = true;
        was[hash3(val)] = true;
        was[hash4(val)] = true;
        was[hash5(val)] = true;
    }

    bool contains( const ULL val ) const {
        if constexpr (use_large_set) {
            return was[hash1(val)] && was[hash2(val)] && was[hash3(val)] && was[hash4(val)] && was[hash5(val)]
            && was[hash6(val)] && was[hash7(val)] && was[hash8(val)] && was[hash9(val)] && was[hash10(val)];
        }
        else {
            return was[hash1(val)] && was[hash2(val)] && was[hash3(val)] && was[hash4(val)] && was[hash5(val)];
            // return was[hash1(val)] && was[hash2(val)];
        }
    }
    bool containsHalf( const ULL val ) const {
        return was[hash1(val)] && was[hash2(val)] && was[hash3(val)] && was[hash4(val)] && was[hash5(val)];
    }

    ULL size() const{ return SZ; }

    void clear(){ fill(ALL(was),false); }

private:
    VB was;
    ULL SZ;

    static constexpr ULL MOD1 = 1'000'000'007;
    static constexpr ULL MOD2 = 1'000'000'009;
    static constexpr ULL MOD3 = 1'000'000'021;
    static constexpr ULL MOD4 = 1'000'000'033;
    static constexpr ULL MOD5 = 1'000'000'087;
    static constexpr ULL MOD6 = 1'000'000'093;
    static constexpr ULL MOD7 = 1'000'000'097;
    static constexpr ULL MOD8 = 1'000'000'103;
    static constexpr ULL MOD9 = 1'000'000'123;
    static constexpr ULL MOD10 = 1'000'000'181;

    unsigned hash1(ULL x) const{ x %= MOD1; return x & (SZ - 1); }
    unsigned hash2(ULL x) const{ x %= MOD2; return ((3 * x) ^ (x >> 1)) & (SZ - 1); }
    unsigned hash3(ULL x) const{ x %= MOD3; return ((5 * x) ^ (x << 1)) & (SZ - 1); }
    unsigned hash4(ULL x) const{ x %= MOD4; return ((7 * x) ^ (x >> 1) ^ (x << 1)) & (SZ - 1);  }
    unsigned hash5(ULL x) const{ x %= MOD5; return ((x >> 1) ^ (x << 1)) & (SZ - 1); }
    unsigned hash6(ULL x) const{ x %= MOD6; return (43 * x) & (SZ - 1); }
    unsigned hash7(ULL x) const{ x %= MOD7; return (13 * x) & (SZ - 1); }
    unsigned hash8(ULL x) const{ x %= MOD8; return (19 * x) & (SZ - 1); }
    unsigned hash9(ULL x) const{ x %= MOD9; return (29 * x) & (SZ - 1); }
    unsigned hash10(ULL x) const{ x %= MOD10; return (37 * x) & (SZ - 1); }
};

/**
 * Special BloomFilter specification for very large instances - it requires much more space
 * (theoretically could be up to 16x more),
 * but uses only 1 access to RAM for insert() and contains()
 * #CAUTION! This only works for 'random' 64-bit integers
 *
 * and it is slower than usual BF and even slower than unordered_set... so sad...
 */
class BloomFilterL {
public:
    static constexpr int SZ = 256;
    static constexpr int SZM = SZ-1;
    /**
     *
     * @param N maximum number of elements that will be stored
     */
    // explicit BloomFilterL(const ULL N ) : was(bit_ceil(N),VB(SZ,false)) {}
    explicit BloomFilterL(const ULL N ) : was(bit_floor(N),VB(SZ,false)) {}

    void insert(const ULL h) { add(h); }

    void add(const ULL val) {
        const int ind = getBucket(val);
        was[ind][hash1(val)] = true;
        was[ind][hash2(val)] = true;
        was[ind][hash3(val)] = true;
        was[ind][hash4(val)] = true;
        was[ind][hash5(val)] = true;
        // was[ind][hash6(val)] = true;
        // was[ind][hash7(val)] = true;
        // was[ind][hash8(val)] = true;
        // was[ind][hash9(val)] = true;
        // was[ind][hash10(val)] = true;
    }

    bool contains( const ULL val ) const {
        const int ind = getBucket(val);
        // return was[ind][hash1(val)] && was[ind][hash2(val)] && was[ind][hash3(val)] && was[ind][hash4(val)] && was[ind][hash5(val)]
        // && was[ind][hash6(val)] && was[ind][hash7(val)] && was[ind][hash8(val)] && was[ind][hash9(val)] && was[ind][hash10(val)];
        return was[ind][hash1(val)] && was[ind][hash2(val)] && was[ind][hash3(val)] && was[ind][hash4(val)] && was[ind][hash5(val)];
        // return was[ind][hash1(val)] && was[ind][hash2(val)] && was[ind][hash3(val)];
    }

    ULL size() const{ return was.size() * SZM; }

    void clear(){ for(auto & v : was) fill(ALL(v),false); }

private:
    VVB was;

    static constexpr ULL MOD1 = 1'000'000'007;
    static constexpr ULL MOD2 = 1'000'000'009;
    static constexpr ULL MOD3 = 1'000'000'021;
    static constexpr ULL MOD4 = 1'000'000'033;
    static constexpr ULL MOD5 = 1'000'000'087;
    static constexpr ULL MOD6 = 1'000'000'093;
    static constexpr ULL MOD7 = 1'000'000'097;
    static constexpr ULL MOD8 = 1'000'000'103;
    static constexpr ULL MOD9 = 1'000'000'123;
    static constexpr ULL MOD10 = 1'000'000'181;

    // unsigned hash1(ULL x) const{ x %= MOD1; return MOD1*x & 511; }
    // unsigned hash2(ULL x) const{ x %= MOD2; return (MOD2*((3 * x) ^ (x >> 1))) & 511; }
    // unsigned hash3(ULL x) const{ x %= MOD3; return (MOD3*((5 * x) ^ (x << 1))) & 511; }
    // unsigned hash4(ULL x) const{ x %= MOD4; return (MOD4*((7 * x) ^ (x >> 1) ^ (x << 1))) & 511;  }
    // unsigned hash5(ULL x) const{ x %= MOD5; return (MOD5*((x >> 1) ^ (x << 1))) & 511; }
    // unsigned hash6(ULL x) const{ x %= MOD6; return (MOD6*(43 * x)) & 511; }
    // unsigned hash7(ULL x) const{ x %= MOD7; return (MOD7*(13 * x)) & 511; }
    // unsigned hash8(ULL x) const{ x %= MOD8; return (MOD8*(19 * x)) & 511; }
    // unsigned hash9(ULL x) const{ x %= MOD9; return (MOD9*(29 * x)) & 511; }
    // unsigned hash10(ULL x) const{ x %= MOD10; return (MOD10*(37 * x)) & 511; }

    unsigned hash1(ULL x) const{ x %= MOD1; return x & SZM; }
    unsigned hash2(ULL x) const{ x %= MOD2; return ((3 * x) ^ (x >> 1)) & SZM; }
    unsigned hash3(ULL x) const{ x %= MOD3; return ((5 * x) ^ (x << 1)) & SZM; }
    unsigned hash4(ULL x) const{ x %= MOD4; return ((7 * x) ^ (x >> 1) ^ (x << 1)) & SZM;  }
    unsigned hash5(ULL x) const{ x %= MOD5; return ((x >> 1) ^ (x << 1)) & SZM; }
    unsigned hash6(ULL x) const{ x %= MOD6; return (43 * x) & SZM; }
    unsigned hash7(ULL x) const{ x %= MOD7; return (13 * x) & SZM; }
    unsigned hash8(ULL x) const{ x %= MOD8; return (19 * x) & SZM; }
    unsigned hash9(ULL x) const{ x %= MOD9; return (29 * x) & SZM; }
    unsigned hash10(ULL x) const{ x %= MOD10; return (37 * x) & SZM; }

    int getBucket(const ULL x) const{
        // return ((MOD1*7 * (x % MOD2)) ^ (MOD3*17 * (x % MOD4))) & (was.size()-1);
        return (((((x*MOD1) % MOD2) * MOD3) % MOD4) * MOD5) & (was.size()-1);
        // return (((x*MOD1) % MOD2) * MOD3) & (was.size()-1);
        // return x & (was.size()-1);
    }
};

VI findReachableNodesFromSWithinDistanceK( VVI & V, VI S, int K );
VI findReachableNodesFromSWithinDistanceK( VVI & V, VI S, int K, VI & dst, VB & was );
VI findFurthestUnreachableNodes( VVI & V, VI S, int K, VB& hit_nodes, int max_unreachables = 100 );
VI findUnreachableNodesWithLargestDegree( VVI & V, VI S, int K, VB& hit_nodes, int max_unreachables = 100, bool include_furthest = false );

template<class _T>
void shuffle( vector<_T> & V, auto & rnd ){
    for( int i=(int)V.size()-1; i>=0; i-- ) swap( V[i], V[rnd.nextInt(i+1)] );
}

volatile extern sig_atomic_t tle;

constexpr bool enable_logs = true;

void terminate(int signum);

void addSigtermCheck();

#endif //PACE25UTILS_H
