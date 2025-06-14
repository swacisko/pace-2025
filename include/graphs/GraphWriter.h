//
// Created by sylwester on 9/5/19.
//

#ifndef ALGORITHMSPROJECT_GRAPHWRITER_H
#define ALGORITHMSPROJECT_GRAPHWRITER_H

#include "Makros.h"

namespace GraphWriter{


    /**
     * Writes graph in strandard format to given stream
     * N M
     * id1 id2
     * ...
     *
     *
     * @param V
     * @param out
     * @param addToId adds this value to id of each node. This is used to convert indexing from 0 to indexing from 1
     */
    extern void writeGraphStandardEdges( VVI & V, ostream & out, int addToId = 0 );

    /**
     * Function writes graph structure to given stream.
     * @param V
     * @param out
     * @param edgeFoolowE If edgeFollowE is true, then edges are written in lines    e id1 id2, otherwise in lines   id1 id2
     * @param addToId adds this value to id of each node. This is used to convert indexing from 0 to indexing from 1
     */
    extern void writeGraphDIMACS( VVI & V, ostream & out, bool edgeFoolowE = false, int addToId = 0 );

}

#endif //ALGORITHMSPROJECT_GRAPHWRITER_H
