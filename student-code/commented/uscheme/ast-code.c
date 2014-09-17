#include "all.h"
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

Def mkDefine(Name name, Lambda lambda) {
    Def n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = DEFINE;
    n->u.define.name = name;
    n->u.define.lambda = lambda;
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

struct Def mkDefineStruct(Name name, Lambda lambda) {
    struct Def n;
    
    n.alt = DEFINE;
    n.u.define.name = name;
    n.u.define.lambda = lambda;
    return n;
}

struct Def mkUseStruct(Name use) {
    struct Def n;
    
    n.alt = USE;
    n.u.use = use;
    return n;
}

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

Exp mkWhilex(Exp cond, Exp body) {
    Exp n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = WHILEX;
    n->u.whilex.cond = cond;
    n->u.whilex.body = body;
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

Exp mkApply(Exp fn, Explist actuals) {
    Exp n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = APPLY;
    n->u.apply.fn = fn;
    n->u.apply.actuals = actuals;
    return n;
}

Exp mkLetx(Letkeyword let, Namelist nl, Explist el, Exp body) {
    Exp n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = LETX;
    n->u.letx.let = let;
    n->u.letx.nl = nl;
    n->u.letx.el = el;
    n->u.letx.body = body;
    return n;
}

Exp mkLambdax(Lambda lambdax) {
    Exp n;
    n = malloc(sizeof(*n));
    assert(n != NULL);
    
    n->alt = LAMBDAX;
    n->u.lambdax = lambdax;
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

struct Exp mkWhilexStruct(Exp cond, Exp body) {
    struct Exp n;
    
    n.alt = WHILEX;
    n.u.whilex.cond = cond;
    n.u.whilex.body = body;
    return n;
}

struct Exp mkBeginStruct(Explist begin) {
    struct Exp n;
    
    n.alt = BEGIN;
    n.u.begin = begin;
    return n;
}

struct Exp mkApplyStruct(Exp fn, Explist actuals) {
    struct Exp n;
    
    n.alt = APPLY;
    n.u.apply.fn = fn;
    n.u.apply.actuals = actuals;
    return n;
}

struct Exp mkLetxStruct(Letkeyword let,
    Namelist nl,
    Explist el,
    Exp body) {
    struct Exp n;
    
    n.alt = LETX;
    n.u.letx.let = let;
    n.u.letx.nl = nl;
    n.u.letx.el = el;
    n.u.letx.body = body;
    return n;
}

struct Exp mkLambdaxStruct(Lambda lambdax) {
    struct Exp n;
    
    n.alt = LAMBDAX;
    n.u.lambdax = lambdax;
    return n;
}

