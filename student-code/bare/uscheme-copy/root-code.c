#include "all.h"
Root mkStackvalueroot(Value *stackvalueroot) {
    Root n;
    
    n.alt = STACKVALUEROOT;
    n.u.stackvalueroot = stackvalueroot;
    return n;
}

Root mkHeaplocroot(Value * *heaplocroot) {
    Root n;
    
    n.alt = HEAPLOCROOT;
    n.u.heaplocroot = heaplocroot;
    return n;
}

Root mkEnvroot(Env *envroot) {
    Root n;
    
    n.alt = ENVROOT;
    n.u.envroot = envroot;
    return n;
}

Root mkExproot(Exp *exproot) {
    Root n;
    
    n.alt = EXPROOT;
    n.u.exproot = exproot;
    return n;
}

Root mkExplistroot(Explist *explistroot) {
    Root n;
    
    n.alt = EXPLISTROOT;
    n.u.explistroot = explistroot;
    return n;
}

Root mkValuelistroot(Valuelist *valuelistroot) {
    Root n;
    
    n.alt = VALUELISTROOT;
    n.u.valuelistroot = valuelistroot;
    return n;
}

Root mkDefroot(Def *defroot) {
    Root n;
    
    n.alt = DEFROOT;
    n.u.defroot = defroot;
    return n;
}

