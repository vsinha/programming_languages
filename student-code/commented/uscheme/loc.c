/*
 * Implementation of memory allocation
 * 
 * To allocate a new location, we call [[malloc]].
 * Chapter [->] describes a much more interesting and
 * efficient implementation of [[allocate]]. [*]
 * <loc.c>=
 */
#include "all.h"

Value* allocate(Value v) {
    Value *loc = malloc(sizeof(*loc));
    assert(loc != NULL);
    *loc = v;
    return loc;
}
/*
 * To use [[malloc]] requires no special initialization
 * or resetting. The funny references to [[envp]] stop
 * compilers from warning that it isn't used.
 * <loc.c>=
 */
void initallocate(Env *envp) {
    (void)(envp);
}
void resetallocate(Env *envp) {
    (void)(envp);
}
