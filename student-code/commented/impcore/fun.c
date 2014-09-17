/*
 * <fun.c>=
 */
#include "all.h"

void printfun(FILE *output, va_list_box *box) {
    Fun f = va_arg(box->ap, Fun);
    switch (f.alt) {
    case PRIMITIVE:
        fprint(output, "<%n>", f.u.primitive);
        break;
    case USERDEF:
        fprint(output, "<userfun (%N) %e>", f.u.userdef.formals,
                                                              f.u.userdef.body);
        break;
    default:
        assert(0);
    }
}
