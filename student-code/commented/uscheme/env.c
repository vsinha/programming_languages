/*
 * Environments
 * 
 * Because environments can be copied, and the copies
 * can be extended, we use a different representation of
 * environments than we used in Impcore. First, and most
 * important, environments are immutable, as we can see
 * from the interface in Section [->]. The operational
 * semantics never mutates an environment, and there is
 * really no need, because all the mutation is done on
 * locations. Moreover, if we wanted to mutate
 * environments, it wouldn't be safe to copy them just
 * by copying pointers; this would make the evaluation
 * of [[lambda]] expressions very expensive.
 * 
 * We choose a representation of environments that makes
 * it easy to share and extend them: an environment
 * contains a single binding and a pointer to the rest
 * of the bindings in the environment. [*]
 * <env.c>=
 */
#include "all.h"

struct Env {
    Name name;
    Value *loc;
    Env tl;
};
/*
 * We look up a name by following [[tl]] pointers. [*]
 * <env.c>=
 */
Value* find(Name name, Env env) {
    for (; env; env = env->tl)
        if (env->name == name)
            return env->loc;
    return NULL;
}
/*
 * Function [[bindalloc]] always creates a new
 * environment with a new binding. There is never any
 * mutation.
 * <env.c>=
 */
Env bindalloc(Name name, Value val, Env env) {
    Env newenv = malloc(sizeof(*newenv));
    assert(newenv != NULL);

    newenv->name = name;
    newenv->loc  = allocate(val);
    newenv->tl   = env;
    return newenv;
}
/*
 * <env.c>=
 */
Env bindalloclist(Namelist nl, Valuelist vl, Env env) {
    for (; nl && vl; nl = nl->tl, vl = vl->tl)
        env = bindalloc(nl->hd, vl->hd, env);
    return env;
}
/*
 * We include [[printenv]] in case it helps you debug
 * your code.
 * <env.c>=
 */
void printenv(FILE *output, va_list_box *box) {
    Env env = va_arg(box->ap, Env);
    char *prefix = " ";

    fprint(output, "{");
    for (; env; env = env->tl) {
        fprint(output, "%s%n -> %v", prefix, env->name, *env->loc);
        prefix = ", ";
    }
    fprint(output, " }");
}
