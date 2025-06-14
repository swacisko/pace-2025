cmake_minimum_required(VERSION 3.15)
project(Pace25)

set(CMAKE_CXX_STANDARD 20)
#SET(CMAKE_CXX_FLAGS "-std=c++20 -O1") # compilation for profiling
#SET(CMAKE_CXX_FLAGS "-D_GLIBCXX_DEBUG -std=c++20 -Wreturn-type -fsanitize=address -O0") # compilation for debugging
#SET(CMAKE_CXX_FLAGS "-D_GLIBCXX_DEBUG -std=c++20 -Wreturn-type -O0") # compilation for debugging

#remove -pthread
#SET(CMAKE_CXX_FLAGS "-static -std=c++20 -O3") # turbo fast
SET(CMAKE_CXX_FLAGS "-std=c++20 -O2") # fully standard-safe fast
#SET(CMAKE_CXX_FLAGS "-std=c++20 -O3 -DNDEBUG") # turbo fast


include_directories(
        include
        include/graphs
        include/graphs/VertexCover/approximation/NuMVC
        include/combinatorics
        include/utils
        include/datastructures
)

file(GLOB SOURCES
        src/graphs/GraphReader.cpp
        src/graphs/GraphWriter.cpp
        src/graphs/generators/GraphGenerator.cpp
        src/graphs/GraphUtils.cpp
        src/graphs/GraphInducer.cpp
        src/graphs/cycles/EulerianCycle.cpp
        src/graphs/components/BridgesAndArtPoints.cpp
        src/graphs/components/ConnctedComponents.cpp
        src/graphs/cliques/CliqueUtils.cpp
        src/graphs/VertexCover/VCUtils.cpp
        src/graphs/scc/StronglyConnectedComponents.cpp
        src/text/CyclicShift.cpp
        src/text/LCP.cpp
        src/combinatorics/GrayCode.cpp
        src/datastructures/BitVector.cpp
        src/combinatorics/CombinatoricUtils.cpp
        src/combinatorics/sequences/permutations/PermutationCreator.cpp
        src/combinatorics/sequences/IntegerSequenceCreator.cpp
        src/combinatorics/sequences/LIS.cpp
        src/datastructures/FAU.cpp
        src/datastructures/Bitset.cpp
        src/datastructures/RandomSelectionSet.cpp
        src/numbertheory/factorization/Factorization.cpp
        src/numbertheory/primes/Primes.cpp
        src/utils/RandomNumberGenerators.cpp
        src/utils/StandardUtils.cpp
        src/utils/TimeMeasurer.cpp
        src/utils/Stopwatch.cpp
        src/geometry/BasicGeometry.cpp
        src/geometry/PointInPolygon.cpp
        src/geometry/PolygonCreator.cpp
        src/geometry/PointsCreator.cpp
        src/visualizations/GVVisualizer.cpp
#        src/graphs/trees/MST.cpp
) # include all source files



add_executable( Pace25DSE ${SOURCES}
        src/CONTESTS/PACE25/HittingSetLS.cpp
        src/CONTESTS/PACE25/HittingSetLS.h
        src/CONTESTS/PACE25/DominatingSetSolver.cpp
        src/CONTESTS/PACE25/DominatingSetSolver.h
#        src/CONTESTS/PACE25/pace25ds_main.cpp
        src/CONTESTS/PACE25/Pace25Utils.cpp
        src/CONTESTS/PACE25/Pace25Utils.h
        src/CONTESTS/PACE25/DSSE.cpp
        src/CONTESTS/PACE25/DSSE.h
        src/CONTESTS/PACE25/GraphRemapper.cpp
        src/CONTESTS/PACE25/GraphRemapper.h
        src/CONTESTS/PACE25/DSReducer.cpp
        src/CONTESTS/PACE25/DSReducer.h
        src/CONTESTS/PACE25/pace25ds_exact_main.cpp
)
#target_link_libraries(Pace25DS PRIVATE OpenMP::OpenMP_CXX stdc++fs)


add_executable( Pace25DSH ${SOURCES}
        src/CONTESTS/PACE25/HittingSetLS.cpp
        src/CONTESTS/PACE25/HittingSetLS.h
        src/CONTESTS/PACE25/DominatingSetSolver.cpp
        src/CONTESTS/PACE25/DominatingSetSolver.h
#        src/CONTESTS/PACE25/pace25ds_main.cpp
        src/CONTESTS/PACE25/Pace25Utils.cpp
        src/CONTESTS/PACE25/Pace25Utils.h
        src/CONTESTS/PACE25/DSSE.cpp
        src/CONTESTS/PACE25/DSSE.h
        src/CONTESTS/PACE25/GraphRemapper.cpp
        src/CONTESTS/PACE25/GraphRemapper.h
        src/CONTESTS/PACE25/DSReducer.cpp
        src/CONTESTS/PACE25/DSReducer.h
        src/CONTESTS/PACE25/pace25ds_heuristic_main.cpp
)


add_executable( Pace25HSE ${SOURCES}
        src/CONTESTS/PACE25/HittingSetLS.cpp
        src/CONTESTS/PACE25/HittingSetLS.h
        src/CONTESTS/PACE25/DominatingSetSolver.cpp
        src/CONTESTS/PACE25/DominatingSetSolver.h
        src/CONTESTS/PACE25/Pace25Utils.cpp
        src/CONTESTS/PACE25/Pace25Utils.h
        src/CONTESTS/PACE25/DSSE.cpp
        src/CONTESTS/PACE25/DSSE.h
        src/CONTESTS/PACE25/GraphRemapper.cpp
        src/CONTESTS/PACE25/GraphRemapper.h
        src/CONTESTS/PACE25/DSReducer.cpp
        src/CONTESTS/PACE25/DSReducer.h
        src/CONTESTS/PACE25/pace25hs_exact_main.cpp
)
#target_link_libraries(Pace25HS PRIVATE OpenMP::OpenMP_CXX stdc++fs)
target_link_libraries(Pace25HSE PRIVATE stdc++fs)



add_executable( Pace25HSH ${SOURCES}
        src/CONTESTS/PACE25/HittingSetLS.cpp
        src/CONTESTS/PACE25/HittingSetLS.h
        src/CONTESTS/PACE25/DominatingSetSolver.cpp
        src/CONTESTS/PACE25/DominatingSetSolver.h
        src/CONTESTS/PACE25/Pace25Utils.cpp
        src/CONTESTS/PACE25/Pace25Utils.h
        src/CONTESTS/PACE25/DSSE.cpp
        src/CONTESTS/PACE25/DSSE.h
        src/CONTESTS/PACE25/GraphRemapper.cpp
        src/CONTESTS/PACE25/GraphRemapper.h
        src/CONTESTS/PACE25/DSReducer.cpp
        src/CONTESTS/PACE25/DSReducer.h
        src/CONTESTS/PACE25/pace25hs_heuristic_main.cpp
)
#target_link_libraries(Pace25HS PRIVATE OpenMP::OpenMP_CXX stdc++fs)
target_link_libraries(Pace25HSH PRIVATE stdc++fs)
