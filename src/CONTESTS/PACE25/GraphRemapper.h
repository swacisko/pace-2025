//
// Created by sylwe on 05/05/2025.
//

#ifndef GRAPHREMAPPER_H
#define GRAPHREMAPPER_H

#include "Pace25Utils.h"

class GraphRemapper {
public:

     static VI createRemappingNodeOrder(VVI & V);
     static VI findDistances(VVI & V, int beg);
     static VI optimizeOrder(VVI & V, VI order);

     static tuple<VVI,VI> remapGraph( VVI & V, VI & order );

private:

    
};

#endif //GRAPHREMAPPER_H
