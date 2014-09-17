/* error.c 587d */
#include "all.h"

jmp_buf errorjmp;

void error(const char *fmt, ...) {
    va_list_box box;

    assert(fmt);
    fflush(stdout);
    fprint(stderr, "error: ");
    va_start(box.ap, fmt);
    vprint(stderr, fmt, &box);
    va_end(box.ap);
    fprint(stderr, "\n");
    fflush(stderr);
    longjmp(errorjmp, 1);   
}
/* error.c 587e */
void checkargc(Exp e, int expected, int actual) {
    if (expected != actual)
        error("expected %d but found %d argument%s in %e",
              expected, actual, actual == 1 ? "" : "s", e);
}
/* error.c 588a */
Name duplicatename(Namelist nl) {
    if (nl != NULL) {
        Name n = nl->hd;
        Namelist tail;
        for (tail = nl->tl; tail; tail = tail->tl)
            if (n == tail->hd)
                return n;
        return duplicatename(nl->tl);
    }
    return NULL;
}
