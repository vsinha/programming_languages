/* ms.c 184a */
#include "all.h"

/* private declarations for mark-and-sweep collection 184b */
typedef struct Mvalue Mvalue;
struct Mvalue {
    Value v;
    unsigned live:1;
};
/* private declarations for mark-and-sweep collection 184c */
enum growth_unit { GROWTH_UNIT = 24 };
typedef struct Arena *Arena;
struct Arena {
    Mvalue pool[GROWTH_UNIT];
    Arena tl;
};
/* private declarations for mark-and-sweep collection 184d */
Arena arenalist, curarena;
Mvalue *hp, *heaplimit;
/* private declarations for mark-and-sweep collection 186a */
static void visitheaploc      (Value *loc);
static void visitstackvalue   (Value v);
static void visitvaluechildren(Value v);
static void visitenv          (Env env);
static void visitvaluelist    (Valuelist vl);
static void visitexp          (Exp exp);
static void visitexplist      (Explist el);
static void visitdef          (Def def);
static void visitroot         (Root r);
/* private declarations for mark-and-sweep collection 791a */
static int nalloc;              /* total number of allocations */
static int ncollections;        /* total number of collections */
static int nmarks;              /* total number of cells marked */
/* ms.c 185a */
static void makecurrent(Arena a) {
    assert(a != NULL);
    curarena = a;
    hp = &a->pool[0];
    heaplimit = &a->pool[GROWTH_UNIT];
}
/* ms.c 185b */
static int heapsize;            /* OMIT */
static void addarena(void) {
    Arena a = calloc(1, sizeof(*a));
    assert(a != NULL);

    if (arenalist == NULL) {
        arenalist = a;
    } else {
        assert(curarena != NULL && curarena->tl == NULL);
        curarena->tl = a;
    }
    makecurrent(a);
    heapsize += GROWTH_UNIT;   /* OMIT */
}
/* ms.c ((prototype)) 185c */
Value* allocloc(void) {
    (void)visitroot; /* eventually the solution will call visitroot(), perhaps
                                                       indirectly */  /* OMIT */
    if (hp == heaplimit)
        addarena();
    assert(hp < heaplimit);
    return &(hp++)->v;
}
/* ms.c 186b */
static void visitenv(Env env) {
    for (; env; env = env->tl)
        visitheaploc(env->loc);
}
/* ms.c ((prototype)) 186d */
static void visitheaploc(Value *loc) {
    Mvalue *m = (Mvalue*)loc;
    if (!m->live) {
        m->live = 1;
        visitvaluechildren(m->v);
    }
}
/* ms.c 186e */
static void visitstackvalue(Value v) {
    visitvaluechildren(v);
}
/* ms.c 187 */
static void visitvaluechildren(Value v) {
    switch (v.alt) {
    case NIL:
    case BOOL:
    case NUM:
    case SYM:
    case PRIMITIVE:
        return;
    case PAIR:
        visitheaploc(v.u.pair.car);
        visitheaploc(v.u.pair.cdr);
        return;
    case CLOSURE:
        visitexp(v.u.closure.lambda.body);
        visitenv(v.u.closure.env);
        return;
    default:
        assert(0);
        return;
    }
}
/* ms.c 622 */
static void visitexp(Exp e) {
    switch (e->alt) {
    case LITERAL:
        visitvaluechildren(e->u.literal);
        return;
    case VAR:
        return;
    case IFX:
        visitexp(e->u.ifx.cond);
        visitexp(e->u.ifx.true);
        visitexp(e->u.ifx.false);
        return;
    case WHILEX:
        visitexp(e->u.whilex.cond);
        visitexp(e->u.whilex.body);
        return;
    case BEGIN:
        visitexplist(e->u.begin);
        return;
    case SET:
        visitexp(e->u.set.exp);
        return;
    case LETX:
        visitexplist(e->u.letx.el);
        visitexp(e->u.letx.body);
        return;
    case LAMBDAX:
        visitexp(e->u.lambdax.body);
        return;
    case APPLY:
        visitexp(e->u.apply.fn);
        visitexplist(e->u.apply.actuals);
        return;
    default:
        assert(0);
    }
}
/* ms.c 623a */
static void visitdef(Def d) {
    if (d == NULL)
        return;
    else
        switch (d->alt) {
        case VAL:
            visitexp(d->u.val.exp);
            return;
        case EXP:
            visitexp(d->u.exp);
            return;
        case DEFINE:
            visitexp(d->u.define.lambda.body);
            return;
        case USE:
            return;
        default:
            assert(0);
        }
}
/* ms.c 623b */
static void visitroot(Root r) {
    switch (r.alt) {
    case STACKVALUEROOT:
        visitstackvalue(*r.u.stackvalueroot);
        return;
    case HEAPLOCROOT:
        visitheaploc(*r.u.heaplocroot);
        return;
    case ENVROOT:
        visitenv(*r.u.envroot);
        return;
    case EXPROOT:
        visitexp(*r.u.exproot);
        return;
    case VALUELISTROOT:
        visitvaluelist(*r.u.valuelistroot);
        return;
    case DEFROOT:
        visitdef(*r.u.defroot);
        return;
    default:
        assert(0);
    }
}
/* ms.c 624a */
static void visitvaluelist(Valuelist vl) {
    for (; vl; vl = vl->tl)
        visitvaluechildren(vl->hd);
}
/* ms.c 624b */
static void visitexplist(Explist el) {
    for (; el; el = el->tl)
        visitexp(el->hd);
}
/* ms.c ((prototype)) 642 */
/* you need to redefine these functions */
void printfinalstats(void) { 
  (void)nalloc; (void)ncollections; (void)nmarks;
  assert(0); 
}
