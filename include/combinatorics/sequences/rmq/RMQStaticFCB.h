//
// Created by sylwester on 9/19/19.
//

#ifndef ALGORITHMSPROJECT_RMQSTATICFCB_H
#define ALGORITHMSPROJECT_RMQSTATICFCB_H

#include "Makros.h"
#include "datastructures/CartesianTree.h"

/**
 * RMQ in O(N) preprocess time and O(1) query time. Only static - no updates possible.
 * This is Farach-Colton and Bender Algorithm.
 * See https://cp-algorithms.com/graph/lca_farachcoltonbender.html for details.
 */
template<class _U>
class RMQStaticFCB{

public:

    /**
     * Constructs RMQ for given array of numbers
     * @param tab
     */
    RMQStaticFCB( vector<_U> & tab ){
        cartesianTree = CartesianTree<_U>(tab);
        adj = cartesianTree.getAdjacency();
//        DEBUG(adj);
        n = tab.size();
        precompute_lca( cartesianTree.getRoot() );
    }

    ~RMQStaticFCB(){}

    /**
     *
     * @param a
     * @param b
     * @return INDEX of the minimum in the range [a,b]
     */
    int query( int a, int b ){
        return lca(a,b);
    }

    static void test(){
//        VI tab = { 2,7,3,1,4,8,5,9   };
//        DEBUG(tab);

        int l_zest = 50;

        while(l_zest--){

            int N = 1e4;
            VI tab;
            for(int i=0; i<N; i++) tab.push_back( rand()% (int)1e9 );


            {
                RMQStaticFCB<int> rmq(tab);


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
//        exit(1);

    }

private:

    CartesianTree<_U> cartesianTree;

    int n;
    vector<vector<int>> adj;

    int block_size, block_cnt;
    vector<int> first_visit;
    vector<int> euler_tour;
    vector<int> height;
    vector<int> log_2;
    vector<vector<int>> st;
    vector<vector<vector<int>>> blocks;
    vector<int> block_mask;

    void dfs(int v, int p, int h) {
        first_visit[v] = euler_tour.size();
        euler_tour.push_back(v);
        height[v] = h;

        for (int u : adj[v]) {
            if (u == p)
                continue;
            dfs(u, v, h + 1);
            euler_tour.push_back(v);
        }
    }

    int min_by_h(int i, int j) {
        return height[euler_tour[i]] < height[euler_tour[j]] ? i : j;
    }

    void precompute_lca(int root) {
        // get euler tour & indices of first occurences
        first_visit.assign(n, -1);
        height.assign(n, 0);
        euler_tour.reserve(2 * n);
        dfs(root, -1, 0);

        // precompute all log values
        int m = euler_tour.size();
        log_2.reserve(m + 1);
        log_2.push_back(-1);
        for (int i = 1; i <= m; i++)
            log_2.push_back(log_2[i / 2] + 1);

        block_size = max(1, log_2[m] / 2);
        block_cnt = (m + block_size - 1) / block_size;

        // precompute minimum of each block and build sparse table
        st.assign(block_cnt, vector<int>(log_2[block_cnt] + 1));
        for (int i = 0, j = 0, b = 0; i < m; i++, j++) {
            if (j == block_size)
                j = 0, b++;
            if (j == 0 || min_by_h(i, st[b][0]) == i)
                st[b][0] = i;
        }
        for (int l = 1; l <= log_2[block_cnt]; l++) {
            for (int i = 0; i < block_cnt; i++) {
                int ni = i + (1 << (l - 1));
                if (ni >= block_cnt)
                    st[i][l] = st[i][l-1];
                else
                    st[i][l] = min_by_h(st[i][l-1], st[ni][l-1]);
            }
        }

        // precompute mask for each block
        block_mask.assign(block_cnt, 0);
        for (int i = 0, j = 0, b = 0; i < m; i++, j++) {
            if (j == block_size)
                j = 0, b++;
            if (j > 0 && (i >= m || min_by_h(i - 1, i) == i - 1))
                block_mask[b] += 1 << (j - 1);
        }

        // precompute RMQ for each unique block
        int possibilities = 1 << (block_size - 1);
        blocks.resize(possibilities);
        for (int b = 0; b < block_cnt; b++) {
            int mask = block_mask[b];
            if (!blocks[mask].empty())
                continue;
            blocks[mask].assign(block_size, vector<int>(block_size));
            for (int l = 0; l < block_size; l++) {
                blocks[mask][l][l] = l;
                for (int r = l + 1; r < block_size; r++) {
                    blocks[mask][l][r] = blocks[mask][l][r - 1];
                    if (b * block_size + r < m)
                        blocks[mask][l][r] = min_by_h(b * block_size + blocks[mask][l][r],
                                                      b * block_size + r) - b * block_size;
                }
            }
        }
    }

    int lca_in_block(int b, int l, int r) {
        return blocks[block_mask[b]][l][r] + b * block_size;
    }

    int lca(int v, int u) {
        int l = first_visit[v];
        int r = first_visit[u];
        if (l > r)
            swap(l, r);
        int bl = l / block_size;
        int br = r / block_size;
        if (bl == br)
            return euler_tour[lca_in_block(bl, l % block_size, r % block_size)];
        int ans1 = lca_in_block(bl, l % block_size, block_size - 1);
        int ans2 = lca_in_block(br, 0, r % block_size);
        int ans = min_by_h(ans1, ans2);
        if (bl + 1 < br) {
            int l = log_2[br - bl - 1];
            int ans3 = st[bl+1][l];
            int ans4 = st[br - (1 << l)][l];
            ans = min_by_h(ans, min_by_h(ans3, ans4));
        }
        return euler_tour[ans];
    }

};

#endif //ALGORITHMSPROJECT_RMQSTATICFCB_H

