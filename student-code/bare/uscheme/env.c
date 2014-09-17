/* env.c 604a */
#include "all.h"

struct Env {
    Name name;
    Value *loc;
    Env tl;
};
/* env.c 604b */
Value* find(Name name, Env env) {
    for (; env; env = env->tl)
        if (env->name == name)
            return env->loc;
    return NULL;
}
/* env.c 604c */
Env bindalloc(Name name, Value val, Env env) {
    Env newenv = malloc(sizeof(*newenv));
    assert(newenv != NULL);

    newenv->name = name;
    newenv->loc  = allocate(val);
    newenv->tl   = env;
    return newenv;
}
/* env.c 604d */
Env bindalloclist(Namelist nl, Valuelist vl, Env env) {
    for (; nl && vl; nl = nl->tl, vl = vl->tl)
        env = bindalloc(nl->hd, vl->hd, env);
    return env;
}
/* env.c 605a */
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
