/* ast.c 601 */
#include "all.h"

void printexp(FILE *output, va_list_box *box) {
    Exp e = va_arg(box->ap, Exp);
    if (e == NULL) {
        fprint(output, "<null>");
        return;
    }

    switch (e->alt){
    case LITERAL:
        fprint(output, "%v", e->u.literal);
        break;
    case VAR:
        fprint(output, "%n", e->u.var);
        break;
    case SET:
        fprint(output, "(set %n %e)", e->u.set.name, e->u.set.exp);
        break;
    case IFX:
        fprint(output, "(if %e %e %e)", e->u.ifx.cond, e->u.ifx.true, e->
                                                                   u.ifx.false);
        break;
    case WHILEX:
        fprint(output, "(while %e %e)", e->u.whilex.cond, e->u.whilex.exp);
        break;
    case BEGIN:
        fprint(output, "(begin%s%E)", e->u.begin?" ":"", e->u.begin);
        break;
    case APPLY:
        fprint(output, "(%n%s%E)", e->u.apply.name,
                      e->u.apply.actuals?" ":"", e->u.apply.actuals);
        break;
    }
}
/* ast.c 602a */
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
        fprint(output, "(define %n (%N) %e)", d->u.define.name,
                      d->u.define.userfun.formals,
              d->u.define.userfun.body);
        break;
    case USE:
        fprint(output, "(use %n)", d->u.use);
        break;
    default:
        assert(0);
    }
}
