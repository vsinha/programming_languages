/* env.c 47e */
#include "all.h"
/* env.c 48a */
struct Valenv {
    Namelist  nl;
    Valuelist vl;
};
/* env.c 48b */
Valenv mkValenv(Namelist nl, Valuelist vl) {
    Valenv e = malloc(sizeof(*e));
    assert(e != NULL);
    assert(lengthNL(nl) == lengthVL(vl));
    e->nl = nl;
    e->vl = vl;
    return e;
}
/* env.c 48c */
static Value* findval(Name name, Valenv env) {
    Namelist  nl;
    Valuelist vl;

    for (nl=env->nl, vl=env->vl; nl && vl; nl=nl->tl, vl=vl->tl)
        if (name == nl->hd)
            return &vl->hd;
    return NULL;
}
/* env.c 48d */
int isvalbound(Name name, Valenv env) {
    return findval(name, env) != NULL;
}
/* env.c 48e */
Value fetchval(Name name, Valenv env) {
    Value *vp = findval(name, env);
    assert(vp != NULL);
    return *vp;
}
/* env.c 49 */
void bindval(Name name, Value val, Valenv env) {
    Value *vp = findval(name, env);
    if (vp != NULL)
        *vp = val;              /* safe optimization */
    else {
        env->nl = mkNL(name, env->nl);
        env->vl = mkVL(val,  env->vl);
    }
}
/* env.c 590b */
struct Funenv {
    Namelist nl;
    Funlist  fl;
};
/* env.c 590c */
Funenv mkFunenv(Namelist nl, Funlist fl) {
    Funenv e = malloc(sizeof *e);
    assert(e != NULL);
    assert(lengthNL(nl) == lengthFL(fl));
    e->nl = nl;
    e->fl = fl;
    return e;
}
/* env.c 590d */
static Fun* findfun(Name name, Funenv env) {
    Namelist nl = env->nl;
    Funlist  fl = env->fl;

    for ( ; nl && fl; nl = nl->tl, fl = fl->tl)
        if (name == nl->hd)
            return &fl->hd;
    return NULL;
}
/* env.c 590e */
int isfunbound(Name name, Funenv env) {
    return findfun(name, env) != NULL;
}
/* env.c 591a */
Fun fetchfun(Name name, Funenv env) {
    Fun *fp = findfun(name, env);
    assert(fp != NULL);
    return *fp;
}
/* env.c 591b */
void bindfun(Name name, Fun fun, Funenv env) {
    Fun *fp = findfun(name, env);
    if (fp != NULL)
        *fp = fun;              /* safe optimization */
    else {
        env->nl = mkNL(name, env->nl);
        env->fl = mkFL(fun,  env->fl);
    }
}
