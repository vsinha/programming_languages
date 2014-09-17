/*
 * Implementing environments
 * 
 * In the interest of type safety, all the environment
 * code is implemented twice: once for value
 * environments and once for function environments. We
 * show only the value-environment code here; the
 * function-environment code appears in Appendix [->].
 * <env.c>=
 */
#include "all.h"
/*
 * We represent an environment as two parallel lists:
 * one holding names and one holding values. It is an
 * invariant of our representation that these lists have
 * the same length.
 * <env.c>=
 */
struct Valenv {
    Namelist  nl;
    Valuelist vl;
};
/*
 * Given the representation, creating an environment is
 * simple. The assertion ensures that our invariant
 * holds at the outset.
 * <env.c>=
 */
Valenv mkValenv(Namelist nl, Valuelist vl) {
    Valenv e = malloc(sizeof(*e));
    assert(e != NULL);
    assert(lengthNL(nl) == lengthVL(vl));
    e->nl = nl;
    e->vl = vl;
    return e;
}
/*
 * Like [[strtoname]], the [[findval]] function uses
 * linear search. Hash tables or search trees would be
 * faster but more complicated.
 * <env.c>=
 */
static Value* findval(Name name, Valenv env) {
    Namelist  nl;
    Valuelist vl;

    for (nl=env->nl, vl=env->vl; nl && vl; nl=nl->tl, vl=vl->tl)
        if (name == nl->hd)
            return &vl->hd;
    return NULL;
}
/*
 * A name is bound if the find function found it.
 * <env.c>=
 */
int isvalbound(Name name, Valenv env) {
    return findval(name, env) != NULL;
}
/*
 * We fetch a value through the pointer returned by
 * [[findval]], if any.
 * <env.c>=
 */
Value fetchval(Name name, Valenv env) {
    Value *vp = findval(name, env);
    assert(vp != NULL);
    return *vp;
}
/*
 * You might think that to add a new binding to an
 * environment, we would always have to insert a new
 * binding at the beginning of the lists. But we can get
 * away with an optimization. If x in dom rho, instead
 * of extending rho by making rho{x |->v}, we can
 * overwrite the old binding of x. This optimization is
 * safe only because no program written in Impcore can
 * tell the difference. We can prove this by examining
 * the rules of the operational semantics, which show
 * that in any context where rho{x |->v} appears, there
 * is no way to get to the old rho(x). (See Exercise 
 * [->].) [*]
 * <env.c>=
 */
void bindval(Name name, Value val, Valenv env) {
    Value *vp = findval(name, env);
    if (vp != NULL)
        *vp = val;              /* safe optimization */
    else {
        env->nl = mkNL(name, env->nl);
        env->vl = mkVL(val,  env->vl);
    }
}
/*
 * Function environments
 * 
 * This code is continued from Chapter [->], which gives
 * the implementation of value environments. Except for
 * types, the code is identical to code in Chapter [->].
 * <env.c>=
 */
struct Funenv {
    Namelist nl;
    Funlist  fl;
};
/*
 * <env.c>=
 */
Funenv mkFunenv(Namelist nl, Funlist fl) {
    Funenv e = malloc(sizeof *e);
    assert(e != NULL);
    assert(lengthNL(nl) == lengthFL(fl));
    e->nl = nl;
    e->fl = fl;
    return e;
}
/*
 * <env.c>=
 */
static Fun* findfun(Name name, Funenv env) {
    Namelist nl = env->nl;
    Funlist  fl = env->fl;

    for ( ; nl && fl; nl = nl->tl, fl = fl->tl)
        if (name == nl->hd)
            return &fl->hd;
    return NULL;
}
/*
 * <env.c>=
 */
int isfunbound(Name name, Funenv env) {
    return findfun(name, env) != NULL;
}
/*
 * <env.c>=
 */
Fun fetchfun(Name name, Funenv env) {
    Fun *fp = findfun(name, env);
    assert(fp != NULL);
    return *fp;
}
/*
 * <env.c>=
 */
void bindfun(Name name, Fun fun, Funenv env) {
    Fun *fp = findfun(name, env);
    if (fp != NULL)
        *fp = fun;              /* safe optimization */
    else {
        env->nl = mkNL(name, env->nl);
        env->fl = mkFL(fun,  env->fl);
    }
}
