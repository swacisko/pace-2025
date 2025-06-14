//
// Created by sylwe on 04/03/2025.
//

#include <GraphReader.h>
#include <Stopwatch.h>
#include "DominatingSetSolver.h"
#include "DSSE.h"
#include "Makros.h"

int main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0);

    addSigtermCheck();


    bool write_result = true;
    bool exact_track = false;
    bool lite_track = false;

    Stopwatch starter;
    string input_reader_opt = "input reader";
    starter.start(input_reader_opt);

    if(write_result && !exact_track) clog.rdbuf(nullptr); // #TEST - stifling all logs


    if constexpr (enable_logs) clog << "Please enter your instance data" << endl;

    VVI V;
    int N,M,K;

    V = GraphReader::readGraphDIMACSWunweighed(cin,false);
    N = V.size(), K = 1;

    starter.stop(input_reader_opt);


    int time_limit_millis = 90'000;
    if(write_result) time_limit_millis = 290'000;
    if(write_result && lite_track) time_limit_millis = 45'000;

    if constexpr (enable_logs) clog << "Reading input took " << starter.getTime(input_reader_opt) / 1000 << " sec." << endl;
    time_limit_millis -= starter.getTime(input_reader_opt);

    time_limit_millis *= 0.99; // take off 1% to finish all necessary computation and hopefully fit in the time limit

    double F = 1.0; // no 21-swaps after HSLS
    int grasp_21swaps_time = (1.0-F) * time_limit_millis;
    time_limit_millis *= F;

    Stopwatch sw;
    sw.setLimit("main", time_limit_millis);
    sw.start("main");


    DominatingSetSolver dss(sw);

    auto res = dss.solveH( V, K, true, time_limit_millis, true, true ); // original

    cout << res.size() << endl;
    if (write_result) {
        for(int d : res) cout << d+1 << "\n";
        cout << flush;
    }

    return 0;
}