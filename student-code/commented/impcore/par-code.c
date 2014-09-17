#include "all.h"
Par mkAtom(Name atom) {
    Par n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = ATOM;
    n->u.atom = atom;
    return n;
}

Par mkList(Parlist list) {
    Par n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = LIST;
    n->u.list = list;
    return n;
}

struct Par mkAtomStruct(Name atom) {
    struct Par n;
    
    n.alt = ATOM;
    n.u.atom = atom;
    return n;
}

struct Par mkListStruct(Parlist list) {
    struct Par n;
    
    n.alt = LIST;
    n.u.list = list;
    return n;
}

