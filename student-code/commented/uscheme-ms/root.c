/*
 * Implementing the root stack
 * 
 * [*] The internal stack is, as mandated by the
 * interface, a pointer to an array of [[Root]]s. We
 * grow it when necessary.
 * <root.c>=
 */
#include "all.h"

Root *rootstack;                /* points to base of the root stack */
int rootstacksize;              /* number of items on the stack now */
static int rootstackmax;        /* max number of items the stack can hold */
/*
 * Private variable [[rootstackmax]] contains the size
 * of the [[rootstack]] array (the maximum number of
 * roots it can hold), while [[rootstacksize]] contains
 * the number of roots actually on the stack.
 */

/*
 * We grow the root stack slowly, by increments of 16.
 * <root.c>=
 */
void pushroot(Root r) {
    if (rootstacksize == rootstackmax) {
        rootstack = realloc(rootstack, sizeof(rootstack[0]) * (rootstackmax + 16
                                                                             ));
        assert(rootstack != NULL);
        rootstackmax += 16;
    }
    rootstack[rootstacksize++] = r;
}
/*
 * Popping a root requires a check that the roots match.
 * We compare pointers by casting to [[void*]].
 * <root.c>=
 */
void poproot(Root r) {
    assert(rootstacksize > 0);
    rootstacksize--;
    assert(rootstack[rootstacksize].alt == r.alt &&
           (void*)rootstack[rootstacksize].u.envroot == (void*)r.u.envroot);
}
/*
 * To reset the root stack, we just reset
 * [[rootstacksize]].
 * <root.c>=
 */
void resetrootstack(void) {
    rootstacksize = 0;
}
