//
// Created by sylwester on 3/24/20.
//

#ifndef ALGORITHMSPROJECT_HEAP_H
#define ALGORITHMSPROJECT_HEAP_H

#include "Makros.h"

/**
 * My implementation of enhanced heap structure. It is a kind of an array with
 * O(1) value lookup at any index
 * O(1) min value lookup,
 * O(logN) push_back time
 * O(logN) min element removal
 * O(logN) (but works relatively fast) update of an element at any index.
 * @tparam _T
 */
template<class _T>
class Heap{

    class Item{
    public:
        Item() = default;
        Item(int itind, int hpind, _T v) : indInHeap(hpind), indInItems(itind), val(v) {}

        int indInItems;
        int indInHeap;
        _T val;
        friend ostream& operator<<(ostream& str, Item& it){
            str << "(v: " << it.val << ", hInd: " << it.indInHeap << ", itInd: " << it.indInItems << ")";
            return str;
        }
    };


public:

    /**
     * Default constructor.
     */
    Heap() = default;

    Heap( function< bool(int&,int&) > eval ){
        heap = vector<Item*>(1,nullptr);
        this->eval = eval;
        this->maxElements = 4;
        items.reserve(maxElements);
    }

    Heap( vector<_T> & it, function< bool(int&,int&) > eval ){
        this->eval = eval;
        this->maxElements = it.size();
        items.clear();

        for( int i=0; i<it.size(); i++ ) items.emplace_back( i,i+1,it[i] );

        heap = vector<Item*>( items.size()+1,nullptr );
        for(int i=0; i<items.size(); i++) heap[i+1] = &items[i];
        validItem = VB(items.size(),true);

        for( int i=0; i<items.size(); i++ ) update(items[i]);

    }

    /**
     * Constructor can be used to initialize array of N objects, with given value
     * @param N
     * @param eval
     */
    Heap( int N, int val, function< bool(int&,int&) > eval ){
        this->eval = eval;
        maxElements = N;
        items.reserve(N);
        for(int i=0; i<N; i++) items.emplace_back(i,i+1,val);
        validItem = VB(N,true);

        heap = vector<Item*>(N+1,nullptr);
        for(int i=0; i<N; i++) heap[i+1] = &items[i];

        // here no need to update items, since all items have the same value.
    }

    ~Heap(){
        for( int i=0; i<heap.size(); i++ ) heap[i] = nullptr;
        validItem.clear();

        vector<Item>().swap(items);
        VB().swap(validItem);
    }

    void clear(){
        heap = vector<Item*>(1, nullptr);
        items.clear();
        validItem.clear();
    }

    bool empty(){ return heap.size() == 1; }
    int size(){ return (int)heap.size()-1; }

    _T& get(int index){
        return items.at(index).val;
    }

    _T& operator[](int ind){ return get(ind); }

    void swapElements(int pos1, int pos2){
        const auto & val1 = get(pos1);
        const auto & val2 = get(pos2);
        set(pos1,val2);
        set(pos2,val1);
    }

    void pop_back(){
        removeFromHeap( items.size()-1 );
    }

    void createNewOfSize(int N, _T val) {
        clear();

        maxElements = N;
        items = vector<Item>(N,val);
        validItem = VB(N,true);
        heap = vector<Item*>(N+1,nullptr);
        for(int i=0; i<N; i++) heap[i+1] = &items[i];
    }

    void createNewOfSizeIota(int N, _T init = 0) {
        clear();

        maxElements = N;
        items = vector<Item>(N);
        for( int i=0; i<N; i++ ) items[i].val = init+i;
        validItem = VB(N,true);
        heap = vector<Item*>(N+1,nullptr);
        for(int i=0; i<N; i++) heap[i+1] = &items[i];
        for( int i=0; i<items.size(); i++ ) update(items[i]);
    }

    /**
     * Removes items at index in (that is items[ind]) from heap, if it is already there
     * @param ind
     */
    void removeFromHeap(int ind){
        if( !validItem[ind] || heap.size() == 1 ) return;
        validItem[ind] = false;

        int indHeap = items[ind].indInHeap;
        items[ind].indInHeap = -1;


        heap[indHeap] = &(*heap.back());
        heap.pop_back();
//        cerr << "removing element " << ind << " in heap index: " << indHeap << "    after removing heap.size(): " << heap.size() << endl;

        if( indHeap < heap.size() ){
            heap[indHeap]->indInHeap = indHeap;
            update( (*heap[indHeap]) );
        }

    }

    /**
     * Sets
     */
    void set(int index, _T value){
        if( !validItem[index] ){
            push_again(index);
        }
        items[index].val = value;
        update( items[index] );
    }

    auto updateElement(int index){ if( validItem[index] ) update(items[index]); }

    void push_back( _T val ){
        if( items.size() == maxElements ){
            vector<Item> newItems;
            newItems.reserve( maxElements << 1 );
            for( int i=0; i<maxElements; i++ ) newItems.push_back( items[i] );
            swap( items, newItems );
//            for(int i=0; i<maxElements; i++) heap[i+1] = &items[ heap[i+1]->indInItems ];
            for(int i=1; i<heap.size(); i++) heap[i] = &items[ heap[i]->indInItems ];
            maxElements <<= 1;
        }

        validItem.push_back(true);
        items.emplace_back( items.size(), heap.size(), val );
        heap.push_back( nullptr );
        heap[ heap.size()-1 ] = &items[ items.size()-1 ];

        update(items.back());
    }

    Item& top(){
        if( heap.size() == 1 ){
            cerr << "top() in empty heap()" << endl; exit(1);
        }
//        return (*heap[1]).val;
        return (*heap[1]);
    }

    /**
     * Extracts minimum value and removes it from heap, then returns that value
     */
    _T& extract_min(){
        int indInItems = heap[1]->indInItems;
        removeFromHeap( indInItems );

        return items[indInItems].val;
    }


    friend ostream& operator<<(ostream& str, Heap<_T> & heap){
        str << "[[ " << endl;
        for( int i=1; i<heap.heap.size(); i++ ){
            if( i > 0 ) str << "  |  ";
            Item* it = heap.heap[i];
            str << (*it) << " valid: " << heap.validItem[it->indInItems];

            str << endl;
        }
        str << " ]]";
        return str;
    }

    Heap<_T>& operator=( const Heap<_T> & oth ){
        eval = oth.eval;
        validItem = oth.validItem;
        items = oth.items;
        heap = vector<Item*>(oth.heap.size(),nullptr);
        for( int i=1; i<heap.size(); i++ ) heap[i] = &items[i-1];
        maxElements = oth.maxElements;
        return *this;
    }

    vector<Item*> heap;

private:

    function< bool(_T&,_T&) > eval;
    VB validItem; // validItem[i] is true, if items[i] is still in the heap, false if it is not in the heap. This way we can remove and place removed items back in the heap some time later
    vector<Item> items;
    int maxElements; // this is the maximum number of elements that can be store in items. If items would grow larger, we have to update pointers in heap, since they would be invalidated due to vector resize

    void update(Item& it){
        if( !up(it) ) down(it);
    }

    /**
     * moves item up in the heap if it can be moved
     * @param it
     * @return true, if element was moved, false otherwise
     */
    bool up( Item& it ){
        int ind = it.indInHeap;
        if( ind == 1 ) return false; // if it is top of the heap

        bool moved = false;
        while( (eval)( it.val,  heap[ ind>>1 ]->val ) ){
            // clog << "while in up(), ind: " << ind << ", it.val: " << it.val << ", heap[ ind>>1 ]->val: " << heap[ ind>>1 ]->val << endl;
            swapItems(it,  *( heap[ ind>>1 ] ) );
            ind = it.indInHeap;
            moved = true;
            if(ind==1) break;
        }

        return moved;
    }

    /**
     * moves item down in the heap if it can be moved
     * @param it
     * @return true if element was moved, false otherwise
     */
    bool down( Item& it ){
        bool moved = false;

        int l = (it.indInHeap << 1);
        int r = l+1;
        int p = r;
        if( p >= heap.size() ) p--; // moving to left son
        if( p >= heap.size() ) return false; // if there is no left son, returning false
        if( p == r && (eval)( heap[l]->val, heap[r]->val ) ) p = l; // if lest son is less than right son

        while( (eval)( heap[p]->val, it.val ) ) {
            // clog << "while in down()" << endl;
            swapItems(it, *(heap[p]) );
            l = it.indInHeap << 1;
            r = l+1;
            p = r;
            if( p >= heap.size() ) p--; // moving to left son
            if( p >= heap.size() ) break; // if there is no left son, returning false
            if( p == r && (eval)( heap[l]->val, heap[r]->val ) ) p = l; // if lest son is less than right son
            moved = true;
        }

        return moved;
    }

    void swapItems( Item& it1, Item& it2 ){
        heap[ it1.indInHeap ] = &it2;
        heap[ it2.indInHeap ] = &it1;
        swap( it1.indInHeap, it2.indInHeap );
    }

    /**
     * Function used to add to the heap element items[item_ind], that was previousle removed from the heap (e.g by removeFromHeap() or extract_min() )
     * @param item_ind
     */
    void push_again( int item_ind ){
        if( validItem[item_ind] == false ){
            validItem[item_ind] = true;
            heap.push_back(nullptr);
            heap[ heap.size()-1 ] = &items[item_ind];
            items[item_ind].indInHeap = heap.size()-1;
        }else{
            cerr << "Element " << items[item_ind] << " still valid but pushed again" << endl;
            exit(1);
        }
    }




};

#endif //ALGORITHMSPROJECT_HEAP_H
