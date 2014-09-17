/* loc.c 141b */
#include "all.h"

Value* allocate(Value v) {
    Value *loc = malloc(sizeof(*loc));
    assert(loc != NULL);
    *loc = v;
    return loc;
}
/* loc.c 141c */
void initallocate(Env *envp) {
    (void)(envp);
}
void resetallocate(Env *envp) {
    (void)(envp);
}
