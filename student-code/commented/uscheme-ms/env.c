/*
 * <env.c>=
 */
#include "all.h"
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
/*
 * This version of [[bindalloclist]] needs to push its
 * [[env]] because it modifies it. Pointers returned by
 * earlier calls to [[bindalloc]] must be reachable from
 * the root stack at subsequent calls to [[bindalloc]].
 * <env.c>=
 */
Env bindalloclist(Namelist nl, Valuelist vl, Env env) {
    pushroot(mkEnvroot(&env));
    for (; nl && vl; nl = nl->tl, vl = vl->tl)
        env = bindalloc(nl->hd, vl->hd, env);
    poproot(mkEnvroot(&env));
    return env;
}
