#include "all.h"
Fun mkUserdef(Userfun userdef) {
    Fun n;
    
    n.alt = USERDEF;
    n.u.userdef = userdef;
    return n;
}

Fun mkPrimitive(Name primitive) {
    Fun n;
    
    n.alt = PRIMITIVE;
    n.u.primitive = primitive;
    return n;
}

