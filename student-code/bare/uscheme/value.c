/* value.c 605b */
#include "all.h"

int istrue(Value v) {
    return v.alt != BOOL || v.u.bool;
}

Value truev, falsev;

void initvalue(void) {
    truev  = mkBool(1);
    falsev = mkBool(0);
}
/* value.c 605c */
Value unspecified (void) {
    switch ((rand()>>4) & 0x3) {
        case 0:  return truev;
        case 1:  return mkNum(rand());
        case 2:  return mkPair(NULL, NULL);
        case 3:  return mkPrimitive(-12, NULL);
        default: return mkNil();
    }
}
/* value.c 606a */
static int nameinlist(Name n, Namelist nl) {
    for (; nl; nl=nl->tl)
        if (n == nl->hd)
            return 1;
    return 0;
}
/* value.c 606b */
static Namelist addname(Name n, Namelist nl) {
    if (nameinlist(n, nl))
        return nl;
    return mkNL(n, nl);
}
/* value.c 606c */
static Namelist addfree(Name n, Namelist bound, Namelist free) {
    if (nameinlist(n, bound))
        return free;
    return addname(n, free);
}
/* value.c 607a */
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
        /* let [[free]] be the free variables for [[e->u.lambdax]] 607b */
        for (nl = e->u.lambdax.formals; nl; nl = nl->tl)
            bound = addname(nl->hd, bound);
        free = freevars(e->u.lambdax.body, bound, free);
        break;
    case LETX:
        /* let [[free]] be the free variables for [[e->u.letx]] 608a */
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
    /* extra cases for finding free variables in {\uscheme} expressions 620f */
    }
    return free;
}
/* value.c 608b */
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
/* value.c 609a */
void printclosure(FILE *output, va_list_box *box) {
    Lambda l = va_arg(box->ap, Lambda);
    Env e    = va_arg(box->ap, Env);
    printclosureat(output, l, e, 1);
}
/* value.c 609b */
static void printvalueat(FILE *output, Value v, int depth);
/* helper functions for [[printvalue]] 610a */
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
/* value.c 609c */
void printvalue(FILE *output, va_list_box *box) {
    printvalueat(output, va_arg(box->ap, Value), 0);
}
/* value.c 610b */
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
