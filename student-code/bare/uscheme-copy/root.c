/* root.c 641a */
#include "all.h"

Root *rootstack;                /* points to base of the root stack */
int rootstacksize;              /* number of items on the stack now */
static int rootstackmax;        /* max number of items the stack can hold */
/* root.c 641b */
void pushroot(Root r) {
    if (rootstacksize == rootstackmax) {
        rootstack = realloc(rootstack, sizeof(rootstack[0]) * (rootstackmax + 16
                                                                             ));
        assert(rootstack != NULL);
        rootstackmax += 16;
    }
    rootstack[rootstacksize++] = r;
}
/* root.c 641c */
void poproot(Root r) {
    assert(rootstacksize > 0);
    rootstacksize--;
    assert(rootstack[rootstacksize].alt == r.alt &&
           (void*)rootstack[rootstacksize].u.envroot == (void*)r.u.envroot);
}
/* root.c 641d */
void resetrootstack(void) {
    rootstacksize = 0;
}
