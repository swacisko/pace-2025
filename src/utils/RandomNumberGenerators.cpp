//
// Created by sylwester on 8/27/19.
//

#include "utils/RandomNumberGenerators.h"


// int UniformIntGenerator::lastSeed = 171'234'573;
atomic<int> UniformIntGenerator::lastSeed = 171'234'573;
// int UniformDoubleGenerator::lastSeed = 232;
atomic<int> UniformDoubleGenerator::lastSeed = 232;