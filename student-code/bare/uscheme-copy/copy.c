/* copy.c 194a */
#include "all.h"

/* private declarations for copying collection 194b */
static Value *fromspace, *tospace;          /* used only at GC time */
static int semispacesize;                   /* size of fromspace and tospace */
/* private declarations for copying collection 194c */
static Value *hp, *heaplimit;               /* used for every allocation */
/* private declarations for copying collection 195a */
static void scanvaluelist(Valuelist vl);
static void scanenv      (Env env);
static void scanexp      (Exp exp);
static void scanexplist  (Explist el);
static void scandef      (Def def);
static void scanvalue    (Value *vp);
static void scanroot     (Root r);
/* private declarations for copying collection 197a */
#define isinspace(LOC, SPACE) ((SPACE) <= (LOC) && (LOC) < (SPACE) +\
                                                                  semispacesize)
static Value *forward(Value *p);
/* private declarations for copying collection 641e */
static void collect(void);
/* copy.c 194d */
int nalloc;   /* OMIT */
Value* allocloc(void) {
    if (hp == heaplimit)
        collect();
    assert(hp < heaplimit);
    nalloc++;   /* OMIT */
    *hp = mkInvalid("allocated but uninitialized");   /* OMIT */
    return hp++;
}
/* copy.c 195d */
static void scanenv(Env env) {
    for (; env; env = env->tl)
        env->loc = forward(env->loc);
}
/* copy.c 196a */
static void scanvalue(Value *vp) {
    switch (vp->alt) {
    case NIL:
    case BOOL:
    case NUM:
    case SYM:
        return;
    case PAIR:
        vp->u.pair.car = forward(vp->u.pair.car);
        vp->u.pair.cdr = forward(vp->u.pair.cdr);
        return;
    case CLOSURE:
        scanexp(vp->u.closure.lambda.body);
        scanenv(vp->u.closure.env);
        return;
    case PRIMITIVE:
        return;
    default:
        assert(0);
        return;
    }
}
/* copy.c 196b */
static Value* forward(Value *p) {
    if (isinspace(p, tospace)) { /* already in to space; must belong to scanned
                                                                         root */
        return p;
    } else {
        assert(isinspace(p, fromspace));
        /* forward pointer [[p]] and return the result 190b */
        if (p->alt == FORWARD) {            /* forwarding pointer */
            assert(isinspace(p->u.forward, tospace));   /* OMIT */
            return p->u.forward;
        } else {
            assert(isinspace(hp, tospace)); /* there is room */   /* OMIT */
            *hp = *p;
            *p  = mkForward(hp);        /* overwrite *p with a new forwarding
                                                                      pointer */
            return hp++;
        }
    }
}
/* copy.c 625 */
static void scanexp(Exp e) {
    switch (e->alt) {
    case LITERAL:
        scanvalue(&e->u.literal);
        break;
    case VAR:
        break;
    case IFX:
        scanexp(e->u.ifx.cond);
        scanexp(e->u.ifx.true);
        scanexp(e->u.ifx.false);
        break;
    case WHILEX:
        scanexp(e->u.whilex.cond);
        scanexp(e->u.whilex.body);
        break;
    case BEGIN:
        scanexplist(e->u.begin);
        break;
    case SET:
        scanexp(e->u.set.exp);
        break;
    case LETX:
        scanexplist(e->u.letx.el);
        scanexp(e->u.letx.body);
        break;
    case LAMBDAX:
        scanexp(e->u.lambdax.body);
        break;
    case APPLY:
        scanexp(e->u.apply.fn);
        scanexplist(e->u.apply.actuals);
        break;
    default:
        assert(0);
    }
}
/* copy.c 626a */
static void scandef(Def d) {
    if (d != NULL)
        switch (d->alt) {
        case EXP:
            scanexp(d->u.exp);
            break;
        case DEFINE:
            scanexp(d->u.define.lambda.body);
            break;
        case VAL:
            scanexp(d->u.val.exp);
            break;
        case USE:
            break;
        default:
            assert(0);
        }
}
/* copy.c 626b */
static void scanroot(Root r) {
    switch (r.alt) {
    case STACKVALUEROOT:
        scanvalue(r.u.stackvalueroot);
        return;
    case HEAPLOCROOT:
        *r.u.heaplocroot = forward(*r.u.heaplocroot);
        return;
    case ENVROOT:
        scanenv(*r.u.envroot);
        return;
    case EXPROOT:
        scanexp(*r.u.exproot);
        return;
    case VALUELISTROOT:
        scanvaluelist(*r.u.valuelistroot);
        return;
    case DEFROOT:
        scandef(*r.u.defroot);
        return;
    default:
        assert(0);
    }
}
/* copy.c 626c */
static void scanvaluelist(Valuelist vl) {
    for (; vl; vl = vl->tl)
        scanvalue(&vl->hd);
}
/* copy.c 627a */
static void scanexplist(Explist el) {
    for (; el; el = el->tl)
        scanexp(el->hd);
}
/* copy.c ((prototype)) 641f */
/* you need to redefine these functions */
void collect(void) { (void)scanroot; assert(0); }
void printfinalstats(void) { assert(0); }
