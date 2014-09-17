/*
 * Values
 * 
 * The implementation of the value interface is not
 * especially interesting. The first part supports
 * Booleans.
 * <value.c>=
 */
#include "all.h"

int istrue(Value v) {
    return v.alt != BOOL || v.u.bool;
}

Value truev, falsev;

void initvalue(void) {
    truev  = mkBool(1);
    falsev = mkBool(0);
}
/*
 * The interface defines a function to return an
 * unspecified value. ``Unspecified'' means we can pick
 * any value we like. For example, we could just always
 * use nil. Unfortunately, if we do that, careless
 * persons will grow to rely on finding nil, and they
 * shouldn't. To foil such carelessness, we choose an
 * unhelpful value at random.
 * <value.c>=
 */
Value unspecified (void) {
    switch ((rand()>>4) & 0x3) {
        case 0:  return truev;
        case 1:  return mkNum(rand());
        case 2:  return mkPair(NULL, NULL);
        case 3:  return mkPrimitive(-12, NULL);
        default: return mkNil();
    }
}
/*
 * With any luck, careless persons' code might make our
 * interpreter dereference a [[NULL]] pointer, which is
 * no worse than such persons deserve.
 */

/*
 * To print a closure nicely, we don't want to print
 * entire environments, but only the parts of the
 * environment that the closure actually depends on?the
 * free variables of the [[lambda]] expression. Finding
 * free variables is hard work. We start with a bunch of
 * utility functions on names. Function [[nameinlist]]
 * says whether a particular [[Name]] is on a
 * [[Namelist]].
 * <value.c>=
 */
static int nameinlist(Name n, Namelist nl) {
    for (; nl; nl=nl->tl)
        if (n == nl->hd)
            return 1;
    return 0;
}
/*
 * Function [[addname]] adds a name to a list, unless
 * it's already there.
 * <value.c>=
 */
static Namelist addname(Name n, Namelist nl) {
    if (nameinlist(n, nl))
        return nl;
    return mkNL(n, nl);
}
/*
 * Function [[freevars]] is passed an expression, a list
 * of variables known to be bound, and a list of
 * variables known to be free. If the expression
 * contains free variables not on either list,
 * [[freevars]] adds them to the free list and returns
 * the new free list. Function [[freevars]] uses
 * function [[addfree]] to do the work.
 * <value.c>=
 */
static Namelist addfree(Name n, Namelist bound, Namelist free) {
    if (nameinlist(n, bound))
        return free;
    return addname(n, free);
}
/*
 * Computing the free variables of an expression is as
 * much work as evaluating the expression. We have to
 * know all the rules for environments.
 * <value.c>=
 */
static Namelist freevars(Exp e, Namelist bound, Namelist free) {
    Namelist nl;
    Explist el;

    switch (e->alt) {
    case LITERAL:
        break;
    case VAR:
        free = addfree(e->u.var, bound, free);
        break;
    case IFX:
        free = freevars(e->u.ifx.cond, bound, free);
        free = freevars(e->u.ifx.true, bound, free);
        free = freevars(e->u.ifx.false, bound, free);
        break;
    case WHILEX:
        free = freevars(e->u.whilex.cond, bound, free);
        free = freevars(e->u.whilex.body, bound, free);
        break;
    case BEGIN:
        for (el = e->u.begin; el; el = el->tl)
            free = freevars(el->hd, bound, free);
        break;
    case SET:
        free = addfree(e->u.set.name, bound, free);
        free = freevars(e->u.set.exp, bound, free);
        break;
    case APPLY:
        free = freevars(e->u.apply.fn, bound, free);
        for (el = e->u.apply.actuals; el; el = el->tl)
            free = freevars(el->hd, bound, free);
        break;
    case LAMBDAX:
        /*
         * The case for lambda expressions is the interesting
         * one. Any variables that are bound by the [[lambda]]
         * are added to the ``known bound'' list for the
         * recursive examination of the [[lambda]]'s body.
         * <let [[free]] be the free variables for [[e->u.lambdax]]>=
         */
        for (nl = e->u.lambdax.formals; nl; nl = nl->tl)
            bound = addname(nl->hd, bound);
        free = freevars(e->u.lambdax.body, bound, free);
        break;
    case LETX:
        /*
         * The let expressions are a bit tricky; we have to
         * follow the rules exactly.
         * <let [[free]] be the free variables for [[e->u.letx]]>=
         */
        switch (e->u.letx.let) {
        case LET:
            for (el = e->u.letx.el; el; el = el->tl)
                free = freevars(el->hd, bound, free);
            for (nl = e->u.letx.nl; nl; nl = nl->tl)
                bound = addname(nl->hd, bound);
            free = freevars(e->u.letx.body, bound, free);
            break;
        case LETSTAR:
            for ( nl = e->u.letx.nl, el = e->u.letx.el
               ; nl && el
               ; nl = nl->tl, el = el->tl
               ) 
            {
                free  = freevars(el->hd, bound, free);
                bound = addname(nl->hd, bound);
            }
            free = freevars(e->u.letx.body, bound, free);
            break;
        case LETREC:
            for (nl = e->u.letx.nl; nl; nl = nl->tl)
                bound = addname(nl->hd, bound);
            for (el = e->u.letx.el; el; el = el->tl)
                free = freevars(el->hd, bound, free);
            free = freevars(e->u.letx.body, bound, free);
            break;
        }
        break;
    /*
     * <extra cases for finding free variables in {\uscheme} expressions>=
     */
    }
    return free;
}
/*
 * Recursive functions are represented by closures whose
 * environments include pointers back to the recursive
 * functions themselves. This means if we always print
 * closures by printing the values of the free
 * variables, the printer could loop forever. The
 * [[depth]] parameter cuts off this loop, so
 * eventually, when [[depth]] reaches 0, the printing
 * functions print closures simply as [[<procedure>]].
 * <value.c>=
 */
static void printnonglobals(FILE *output, Namelist nl, Env env, int depth);

static void printclosureat(FILE *output, Lambda lambda, Env env, int depth) {
    if (depth > 0) {
        Namelist vars = freevars(lambda.body, lambda.formals, NULL);
        fprint(output, "<%\\, {", lambda);
        printnonglobals(output, vars, env, depth - 1);
        fprint(output, "}>");
    } else {
        fprint(output, "<procedure>");
    }
}
/*
 * <value.c>=
 */
void printclosure(FILE *output, va_list_box *box) {
    Lambda l = va_arg(box->ap, Lambda);
    Env e    = va_arg(box->ap, Env);
    printclosureat(output, l, e, 1);
}
/*
 * The value-printing functions also need a [[depth]]
 * parameter.
 * <value.c>=
 */
static void printvalueat(FILE *output, Value v, int depth);
/*
 * Function [[printtail]] handles the correct printing
 * of lists. If a cons cell doesn't have another cons
 * cell or [[NIL]] in its [[cdr]] field, the [[car]] and
 * [[cdr]] are separated by a dot.
 * <helper functions for [[printvalue]]>=
 */
static void printtail(FILE *output, Value v, int depth) {
    switch (v.alt) {
    case NIL:
        fprint(output, ")");
        break;
    case PAIR:
        fprint(output, " ");
        printvalueat(output, *v.u.pair.car, depth);
        printtail(output, *v.u.pair.cdr, depth);
        break;
    default:
        fprint(output, " . ");
        printvalueat(output, v, depth);
        fprint(output, ")");
        break;
    }
}
static void printvalueat(FILE *output, Value v, int depth) {
    switch (v.alt){
    case NIL:
        fprint(output, "()");
        return;
    case BOOL:
        fprint(output, v.u.bool ? "#t" : "#f");
        return;
    case NUM:
        fprint(output, "%d", v.u.num);
        return;
    case SYM:
        fprint(output, "%n", v.u.sym);
        return;
    case PRIMITIVE:
        fprint(output, "<procedure>");
        return;
    case PAIR:
        fprint(output, "(");
        printvalueat(output, *v.u.pair.car, depth);
        printtail(output, *v.u.pair.cdr, depth);
        return;
    case CLOSURE:
        printclosureat(output, v.u.closure.lambda, v.u.closure.env, depth);
        return;
    default:
        fprint(output, "<unknown v.alt=%d>", v.alt);
return;        assert(0);
    }
}
/*
 * The default depth is 0; that is, by default the
 * interpreter doesn't print closures at all. By
 * changing this default depth, you can get more
 * information.
 * <value.c>=
 */
void printvalue(FILE *output, va_list_box *box) {
    printvalueat(output, va_arg(box->ap, Value), 0);
}
/*
 * Finally, the implementation of [[printnonglobals]].
 * <value.c>=
 */
Env *globalenv;
static void printnonglobals(FILE *output, Namelist nl, Env env, int depth) {
    char *prefix = "";
    for (; nl; nl = nl->tl) {
        Value *loc = find(nl->hd, env);
        if (loc && (globalenv == NULL || find(nl->hd, *globalenv) != loc)) {
            fprint(output, "%s%n -> ", prefix, nl->hd);
            prefix = ", ";
            printvalueat(output, *loc, depth);
        }
    }
}
