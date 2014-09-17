/*
 * Expressions
 * 
 * Here is the (boring) code that prints abstract-syntax
 * trees.
 * <ast.c>=
 */
#include "all.h"
/*
 * <ast.c>=
 */
void printdef(FILE *output, va_list_box *box) {
    Def d = va_arg(box->ap, Def);
    if (d == NULL) {
        fprint(output, "<null>");
        return;
    }

    switch (d->alt) {
    case VAL:
        fprint(output, "(val %n %e)", d->u.val.name, d->u.val.exp);
        break;
    case EXP:
        fprint(output, "%e", d->u.exp);
        break;
    case DEFINE:
        fprint(output, "(define %n %\\)", d->u.define.name, d->u.define.lambda);
        break;
    case USE:
        fprint(output, "(use %n)", d->u.use);
        break;
    default:
        assert(0);
    }
}
/*
 * <ast.c>=
 */
static void printlet(FILE *output, Exp let) {
    Namelist nl;
    Explist el;

    switch (let->u.letx.let) {
    case LET:
        fprint(output, "(let (");
        break;
    case LETSTAR:
        fprint(output, "(let* (");
        break;
    case LETREC:
        fprint(output, "(letrec (");
        break;
    default:
        assert(0);
    }
    for (nl = let->u.letx.nl, el = let->u.letx.el; 
         nl && el;
         nl = nl->tl, el = el->tl)
        fprint(output, "(%n %e)%s", nl->hd, el->hd, nl->tl?" ":"");
    fprint(output, ") %e)", let->u.letx.body);
}   
/*
 * <ast.c>=
 */
void printexp(FILE *output, va_list_box *box) {
    Exp e = va_arg(box->ap, Exp);
    if (e == NULL) {
        fprint(output, "<null>");
        return;
    }

    switch (e->alt) {
    case LITERAL:
        if (e->u.literal.alt == NUM || e->u.literal.alt == BOOL)
            fprint(output, "%v", e->u.literal);
        else
            fprint(output, "'%v", e->u.literal);
        break;
    case VAR:
        fprint(output, "%n", e->u.var);
        break;
    case IFX:
        fprint(output, "(if %e %e %e)", e->u.ifx.cond, e->u.ifx.true, e->
                                                                   u.ifx.false);
        break;
    case WHILEX:
        fprint(output, "(while %e %e)", e->u.whilex.cond, e->u.whilex.body);
        break;
    case BEGIN:
        fprint(output, "(begin%s%E)", e->u.begin ? " " : "", e->u.begin);
        break;
    case SET:
        fprint(output, "(set %n %e)", e->u.set.name, e->u.set.exp);
        break;
    case LETX:
        printlet(output, e);
        break;
    case LAMBDAX:
        fprint(output, "%\\", e->u.lambdax);
        break;
    case APPLY:
        fprint(output, "(%e%s%E)", e->u.apply.fn,
              e->u.apply.actuals ? " " : "", e->u.apply.actuals);
        break;
    /*
     * Future work
     * 
     * These empty definitions are placeholders for future
     * work in which Chapter [->] will be split into two
     * chapters: one on a new interpreter for micro-Scheme
     * that uses a stack-based abstract machine, and one on
     * a garbage collector that works with that new
     * interpreter.
     * 
     * <extra cases for printing {\uscheme} ASTs>=
     */
    }
}
/*
 * <ast.c>=
 */
void printlambda(FILE *output, va_list_box *box) {
    Lambda l = va_arg(box->ap, Lambda);
    fprint(output, "(lambda (%N) %e)", l.formals, l.body);
}
