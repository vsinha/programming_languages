/* loc.c 182d */
#include "all.h"

Value* allocate(Value v) {
    Value *loc;

    pushroot(mkStackvalueroot(&v));
    loc = allocloc();
    assert(loc != NULL);
    poproot(mkStackvalueroot(&v));
    *loc = v;
    return loc;
}
/* loc.c 183a */
extern void printfinalstats(void);   /*OMIT*/
void initallocate(Env *envp) {
    atexit(printfinalstats);         /*OMIT*/
    pushroot(mkEnvroot(envp));
    *envp = NULL;
}
/* loc.c 183b */
void resetallocate(Env *envp) {
    resetrootstack();
    pushroot(mkEnvroot(envp));
}
/* loc.c 627b */
int gammadesired(int defaultval, int minimum) {
    Value *gloc;

    assert(rootstacksize > 0 && rootstack[0].alt == ENVROOT);
    gloc = find(strtoname("&gamma-desired"), *rootstack[0].u.envroot);
    if (gloc && gloc->alt == NUM)
        return gloc->u.num > minimum ? gloc->u.num : minimum;
    else
        return defaultval;
}
/* loc.c 627e */
Value validate(Value v) {
    assert(v.alt != INVALID);
    return v;
}
