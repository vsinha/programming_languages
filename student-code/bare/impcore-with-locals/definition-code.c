#include "all.h"
Userfun mkUserfun(Namelist formals, Namelist locals, Exp body) {
    Userfun n;
    
    n.formals = formals;
    n.locals = locals;
    n.body = body;
    return n;
}

Def mkVal(Name name, Exp exp) {
    Def n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = VAL;
    n->u.val.name = name;
    n->u.val.exp = exp;
    return n;
}

Def mkExp(Exp exp) {
    Def n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = EXP;
    n->u.exp = exp;
    return n;
}

Def mkDefine(Name name, Userfun userfun) {
    Def n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = DEFINE;
    n->u.define.name = name;
    n->u.define.userfun = userfun;
    return n;
}

Def mkUse(Name use) {
    Def n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = USE;
    n->u.use = use;
    return n;
}

struct Def mkValStruct(Name name, Exp exp) {
    struct Def n;
    
    n.alt = VAL;
    n.u.val.name = name;
    n.u.val.exp = exp;
    return n;
}

struct Def mkExpStruct(Exp exp) {
    struct Def n;
    
    n.alt = EXP;
    n.u.exp = exp;
    return n;
}

struct Def mkDefineStruct(Name name, Userfun userfun) {
    struct Def n;
    
    n.alt = DEFINE;
    n.u.define.name = name;
    n.u.define.userfun = userfun;
    return n;
}

struct Def mkUseStruct(Name use) {
    struct Def n;
    
    n.alt = USE;
    n.u.use = use;
    return n;
}

