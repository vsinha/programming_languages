/*
 * Implementation of the micro-Scheme allocation
 * interface
 * 
 * As a small illustration of the use of the root stack,
 * we show how to use the heap interface to implement
 * the allocation interface defined in Chapter [->]. The
 * copying and mark-and-sweep collectors use different
 * implementations of [[allocloc]], but they share this
 * implementation of [[allocate]]. [*]
 * <loc.c>=
 */
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
/*
 * The interesting part is that [[allocloc]] might make
 * objects on the heap move, so before we call
 * [[allocloc]], we have to put [[v]] on the root stack.
 * This way, if [[v]] is a pair, its [[car]] and [[cdr]]
 * fields are sure to be updated correctly.
 */

/*
 * One should call [[initallocate]] only at startup
 * time. It pushes an environment onto the root stack,
 * and it sets the environment to [[NULL]] so there
 * won't be a pointer to an uninitialized environment on
 * the root stack.
 * <loc.c>=
 */
extern void printfinalstats(void);   /*OMIT*/
void initallocate(Env *envp) {
    atexit(printfinalstats);         /*OMIT*/
    pushroot(mkEnvroot(envp));
    *envp = NULL;
}
/*
 * Function [[resetallocate]] simply adjusts the stack.
 * <loc.c>=
 */
void resetallocate(Env *envp) {
    resetrootstack();
    pushroot(mkEnvroot(envp));
}
/*
 * Other supporting code
 * 
 * To control the size of the heap, we might want to use
 * the micro-Scheme variable [[ --- gamma-desired]], as
 * described in Exercises [->] and [->]. This routine
 * gets the value of that variable. [*]
 * <loc.c>=
 */
int gammadesired(int defaultval, int minimum) {
    Value *gloc;

    assert(rootstacksize > 0 && rootstack[0].alt == ENVROOT);
    gloc = find(strtoname("&gamma-desired"), *rootstack[0].u.envroot);
    if (gloc && gloc->alt == NUM)
        return gloc->u.num > minimum ? gloc->u.num : minimum;
    else
        return defaultval;
}
/*
 * <loc.c>=
 */
Value validate(Value v) {
    assert(v.alt != INVALID);
    return v;
}
