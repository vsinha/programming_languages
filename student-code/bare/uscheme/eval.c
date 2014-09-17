/* eval.c 128c */
#include "all.h"

/* eval.c declarations 130e */
static Valuelist evallist(Explist el, Env env);
/* eval.c 129a */
Value eval(Exp e, Env env) {
    checkoverflow(1000000 * sizeof(char *)); /* OMIT */
    switch (e->alt) {
    case LITERAL:
        /* evaluate [[e->u.literal]] and return the result 129b */
        return e->u.literal;
    case VAR:   
        /* evaluate [[e->u.var]] and return the result 129c */
        if (find(e->u.var, env) == NULL)
            error("variable %n not found", e->u.var);
        return *find(e->u.var, env);
    case SET:
        /* evaluate [[e->u.set]] and return the result 129d */
        if (find(e->u.set.name, env) == NULL)
            error("set unbound variable %n", e->u.set.name);
        return *find(e->u.set.name, env) = eval(e->u.set.exp, env);
    case IFX:
        /* evaluate [[e->u.ifx]] and return the result 133a */
        if (istrue(eval(e->u.ifx.cond, env)))
            return eval(e->u.ifx.true, env);
        else
            return eval(e->u.ifx.false, env);
    case WHILEX:
        /* evaluate [[e->u.whilex]] and return the result 133b */
        while (istrue(eval(e->u.whilex.cond, env)))
            eval(e->u.whilex.body, env);
        return falsev;
    case BEGIN:
        /* evaluate [[e->u.begin]] and return the result 133c */
        {
            Explist el;
            Value v = falsev;
            for (el = e->u.begin; el; el = el->tl)
                v = eval(el->hd, env);
            return v;
        }
    case APPLY:
        /* evaluate [[e->u.apply]] and return the result 130b */
        {
            Value     f  = eval    (e->u.apply.fn,      env);
            Valuelist vl = evallist(e->u.apply.actuals, env);

            switch (f.alt) {
            case PRIMITIVE:
                /* apply [[f.u.primitive]] to [[vl]] and return the result 130c
                                                                              */
                return f.u.primitive.function(e, f.u.primitive.tag, vl);
            case CLOSURE:
                /* apply [[f.u.closure]] to [[vl]] and return the result 130d */
                {
                    Namelist nl = f.u.closure.lambda.formals;
                    checkargc(e, lengthNL(nl), lengthVL(vl));
                    return eval(f.u.closure.lambda.body,
                                bindalloclist(nl, vl, f.u.closure.env));
                }
            default:
                error("%e evaluates to non-function %v in %e", e->u.apply.fn, f,
                                                                             e);
            }
        }
    case LETX:
        /* evaluate [[e->u.letx]] and return the result 131b */
        switch (e->u.letx.let) {
        case LET:
            /* if [[e->u.letx.nl]] contains a duplicate, complain of error in
                                                                 [[let]] 610d */
            if (duplicatename(e->u.letx.nl) != NULL)
                error("bound name %n appears twice in let", duplicatename(e->
                                                                    u.letx.nl));
            /* extend [[env]] by simultaneously binding [[el]] to [[nl]] 131c */
            env = bindalloclist(e->u.letx.nl, evallist(e->u.letx.el, env), env);
            break;
        case LETSTAR:
            /* extend [[env]] by sequentially binding [[el]] to [[nl]] 132a */
            {
                Namelist nl;
                Explist el;

                for (nl = e->u.letx.nl, el = e->u.letx.el;
                     nl && el;
                     nl = nl->tl, el = el->tl)
                    env = bindalloc(nl->hd, eval(el->hd, env), env);
                assert(nl == NULL && el == NULL);
            }
            break;
        case LETREC:
            /* if [[e->u.letx.nl]] contains a duplicate, complain of error in
                                                              [[letrec]] 610e */
            if (duplicatename(e->u.letx.nl) != NULL)
                error("bound name %n appears twice in letrec", duplicatename(e->
                                                                    u.letx.nl));
            /* extend [[env]] by recursively binding [[el]] to [[nl]] 132b */
            {
                Namelist nl;
                Valuelist vl;

                for (nl = e->u.letx.nl; nl; nl = nl->tl)    
                    env = bindalloc(nl->hd, unspecified(), env);
                vl = evallist(e->u.letx.el, env);
                for (nl = e->u.letx.nl;
                     nl && vl;
                     nl = nl->tl, vl = vl->tl)
                    *find(nl->hd, env) = vl->hd;
            }
            break;
        default:
            assert(0);
        }
        return eval(e->u.letx.body, env);
    case LAMBDAX:
        /* evaluate [[e->u.lambdax]] and return the result 130a */
        /* if [[e->u.lambdax.formals]] contains a duplicate, call [[error]] 610c
                                                                              */
        if (duplicatename(e->u.lambdax.formals) != NULL)
            error("formal parameter %n appears twice in lambda",
                  duplicatename(e->u.lambdax.formals));
        return mkClosure(e->u.lambdax, env);
    }
    assert(0);
    return falsev;
}
/* eval.c 131a */
static Valuelist evallist(Explist el, Env env) {
    if (el == NULL) {
        return NULL;
    } else {
        Value v = eval(el->hd, env);      /* enforce uScheme's order of
                                                                   evaluation */
        return mkVL(v, evallist(el->tl, env));
    }
}
