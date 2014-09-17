#include "all.h"
Exp mkLiteral(Value literal) {
    Exp n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = LITERAL;
    n->u.literal = literal;
    return n;
}

Exp mkVar(Name var) {
    Exp n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = VAR;
    n->u.var = var;
    return n;
}

Exp mkSet(Name name, Exp exp) {
    Exp n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = SET;
    n->u.set.name = name;
    n->u.set.exp = exp;
    return n;
}

Exp mkIfx(Exp cond, Exp true, Exp false) {
    Exp n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = IFX;
    n->u.ifx.cond = cond;
    n->u.ifx.true = true;
    n->u.ifx.false = false;
    return n;
}

Exp mkWhilex(Exp cond, Exp exp) {
    Exp n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = WHILEX;
    n->u.whilex.cond = cond;
    n->u.whilex.exp = exp;
    return n;
}

Exp mkBegin(Explist begin) {
    Exp n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = BEGIN;
    n->u.begin = begin;
    return n;
}

Exp mkApply(Name name, Explist actuals) {
    Exp n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = APPLY;
    n->u.apply.name = name;
    n->u.apply.actuals = actuals;
    return n;
}

struct Exp mkLiteralStruct(Value literal) {
    struct Exp n;
    
    n.alt = LITERAL;
    n.u.literal = literal;
    return n;
}

struct Exp mkVarStruct(Name var) {
    struct Exp n;
    
    n.alt = VAR;
    n.u.var = var;
    return n;
}

struct Exp mkSetStruct(Name name, Exp exp) {
    struct Exp n;
    
    n.alt = SET;
    n.u.set.name = name;
    n.u.set.exp = exp;
    return n;
}

struct Exp mkIfxStruct(Exp cond, Exp true, Exp false) {
    struct Exp n;
    
    n.alt = IFX;
    n.u.ifx.cond = cond;
    n.u.ifx.true = true;
    n.u.ifx.false = false;
    return n;
}

struct Exp mkWhilexStruct(Exp cond, Exp exp) {
    struct Exp n;
    
    n.alt = WHILEX;
    n.u.whilex.cond = cond;
    n.u.whilex.exp = exp;
    return n;
}

struct Exp mkBeginStruct(Explist begin) {
    struct Exp n;
    
    n.alt = BEGIN;
    n.u.begin = begin;
    return n;
}

struct Exp mkApplyStruct(Name name, Explist actuals) {
    struct Exp n;
    
    n.alt = APPLY;
    n.u.apply.name = name;
    n.u.apply.actuals = actuals;
    return n;
}

