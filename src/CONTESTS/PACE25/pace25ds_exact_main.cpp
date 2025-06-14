//
// Created by sylwe on 04/03/2025.
//

#include <GraphInducer.h>
#include <GraphUtils.h>
#include <GraphReader.h>
#include <Stopwatch.h>
#include <generators/GraphGenerator.h>

#include "DominatingSetSolver.h"
#include "DSSE.h"
#include "Makros.h"


int main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0);

    addSigtermCheck();


    constexpr bool write_result = true;

    Stopwatch starter;
    string input_reader_opt = "input reader";
    starter.start(input_reader_opt);

    if(write_result) clog.rdbuf(nullptr);

    if constexpr (enable_logs) clog << "Please enter your instance data" << endl;

    VVI V;
    int N,M,K;


    V = GraphReader::readGraphDIMACSWunweighed(cin,false);
    N = V.size(), K = 1;

    starter.stop(input_reader_opt);

    Stopwatch sw;
    sw.start("main");

    DSSE dsse(V);
    clog << "Finding optimal result, this may take some time..." << endl;
    dsse.exact_hs_solving_method = CPSAT;
    auto res_opt = dsse.solve(true, true, false); // use reductions

    sw.stop("main");
    if constexpr (enable_logs) DEBUG(res_opt.size());
    assert(DSS::isCorrect(V,res_opt,K));
    if constexpr (enable_logs) sw.writeAll();

    cout << res_opt.size() << endl;
    if (write_result) {
        for(int d : res_opt) cout << d+1 << "\n";
        cout << flush;
    }

    return 0;
}