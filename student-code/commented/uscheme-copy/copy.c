/*
 * Prototype of a copying system for micro-Scheme
 * 
 * Here we present more of the details of copying
 * collection for micro-Scheme. Further details appear
 * in Section [->], and to get a complete system, you
 * can work Exercises [->] through [->].
 * <copy.c>=
 */
#include "all.h"

/*
 * The semispaces [[fromspace]] and [[tospace]] each
 * have size [[semispacesize]].
 * <private declarations for copying collection>=
 */
static Value *fromspace, *tospace;          /* used only at GC time */
static int semispacesize;                   /* size of fromspace and tospace */
/*
 * We always allocate from [[fromspace]]. The heap
 * pointer [[hp]] points to the next location available
 * to be allocated, and [[heaplimit]] points just past
 * the last location available to be allocated. The
 * number of locations that can be allocated before the
 * next collection is [[heaplimit - hp]].
 * <private declarations for copying collection>=
 */
static Value *hp, *heaplimit;               /* used for every allocation */
/*
 * Tracing roots
 * 
 * [*] Just as the mark-and-sweep system has a visiting
 * procedure for each type of potential root, the
 * copying system has a scanning procedure for each type
 * of potential root.
 * <private declarations for copying collection>=
 */
static void scanvaluelist(Valuelist vl);
static void scanenv      (Env env);
static void scanexp      (Exp exp);
static void scanexplist  (Explist el);
static void scandef      (Def def);
static void scanvalue    (Value *vp);
static void scanroot     (Root r);
/*
 * The function [[scanroot]] looks at the tag of a root
 * and calls the appropriate scanning procedure.
 */

/*
 * <private declarations for copying collection>=
 */
#define isinspace(LOC, SPACE) ((SPACE) <= (LOC) && (LOC) < (SPACE) +\
                                                                  semispacesize)
static Value *forward(Value *p);
/*
 * A more aggressive collector would probably compute
 * [[isinspace]] with a single comparison (Exercise [->]
 * ).
 */

/*
 * Placeholders for exercises
 * 
 * <private declarations for copying collection>=
 */
static void collect(void);
/*
 * Allocation
 * 
 * In a copying system, the allocator is very simple. In
 * real systems, [[hp]] is in a register, and
 * [[allocloc]] is inlined. [*]
 * <copy.c>=
 */
int nalloc;   /* OMIT */
Value* allocloc(void) {
    if (hp == heaplimit)
        collect();
    assert(hp < heaplimit);
    nalloc++;   /* OMIT */
    *hp = mkInvalid("allocated but uninitialized");   /* OMIT */
    return hp++;
}
/*
 * The assertion can help detect bugs in a heap-growth
 * algorithm.
 */

/*
 * [*] The implementations of our scanning procedures
 * are more complicated than they would be in real life.
 * In a real system, these scanning procedures would
 * simply forward internal pointers. In our system,
 * because only [[Value]] objects are allocated on the
 * heap, we have a hybrid of forwarding and graph
 * traversal. As before, we use [[Env]] to illustrate;
 * we forward the [[loc]] pointer but traverse the
 * [[tl]] pointer.
 * <copy.c>=
 */
static void scanenv(Env env) {
    for (; env; env = env->tl)
        env->loc = forward(env->loc);
}
/*
 * Here is the code to scan values. Again we forward
 * pointers of type [[Value*]] but traverse other
 * pointers. [*]
 * <copy.c>=
 */
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
/*
 * The complete implementation of [[forward]] has one
 * more subtlety; in our system, the same root can
 * appear on the root stack more than once. [This
 * doesn't happen in real systems, because with compiler
 * support, things naturally fall out such that each
 * root is scanned \emph{exactly} once. In our
 * interpreter, without compiler support, it is much
 * easier to ensure only that each root appears on the
 * stack \emph{at least} once.] If we scan such a root
 * for a second time, its internal pointers already
 * point to to-space. We need to test for this
 * possibility so we don't try to forward a pointer that
 * already points to to-space.
 * <copy.c>=
 */
static Value* forward(Value *p) {
    if (isinspace(p, tospace)) { /* already in to space; must belong to scanned
                                                                         root */
        return p;
    } else {
        assert(isinspace(p, fromspace));
        /*
         * The basic operation used in a copying collector is
         * forwarding a pointer. This operation takes a pointer
         * to an object in from-space and returns a pointer to
         * the unique copy of that object in to-space. The code
         * is very simple; [[p]] is a pointer into from-space,
         * and we copy the object [[*p]] unless it has been
         * copied already. We copy the object to [[*hp]], which
         * is safe because while pointers are being forwarded,
         * [[hp]] points into to-space, at the boundary between
         * allocated and unallocated locations. Because to-space
         * is as big as from-space, and because no object is
         * copied more than once, there is guaranteed to be
         * enough room to hold all the objects.
         * <forward pointer [[p]] and return the result>=
         */
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
/*
 * We make [[isinspace]] a macro because measurements
 * show it contributes significantly to
 * garbage-collection time. [*]
 */

/*
 * Scanning expressions means scanning internal values
 * or subexpressions.
 * <copy.c>=
 */
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
/*
 * Scanning definitions means scanning their
 * expressions.
 * <copy.c>=
 */
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
/*
 * Scanning roots means calling the appropriate scanning
 * procedures, with one exception; a [[HEAPLOCROOT]],
 * which is a pointer directly to an object on the heap,
 * has to be forwarded.
 * <copy.c>=
 */
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
/*
 * Scanning lists is straightforward.
 * <copy.c>=
 */
static void scanvaluelist(Valuelist vl) {
    for (; vl; vl = vl->tl)
        scanvalue(&vl->hd);
}
/*
 * <copy.c>=
 */
static void scanexplist(Explist el) {
    for (; el; el = el->tl)
        scanexp(el->hd);
}
/*
 * <copy.c ((prototype))>=
 */
/* you need to redefine these functions */
void collect(void) { (void)scanroot; assert(0); }
void printfinalstats(void) { assert(0); }
