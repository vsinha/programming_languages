/* eval.c 628 */
#include "all.h"

/* eval.c declarations 631d */
static Valuelist evallist(Explist el, Env env);
/* eval.c 629a */
Value eval(Exp e, Env env) {
    checkoverflow(1000000 * sizeof(char *)); /* OMIT */
    switch (e->alt) {
    case LITERAL:
        /* evaluate [[e->u.literal]] and return 629b */
        return e->u.literal;
    case VAR:   
        /* evaluate [[e->u.var]] and return 629c */
        if (find(e->u.var, env) == NULL)
            error("variable %n not found", e->u.var);
        return *find(e->u.var, env);
    case SET:
        /* evaluate [[e->u.set]] and return 630a */
        {
            Value v;

            if (find(e->u.set.name, env) == NULL)
                error("set unbound variable %n", e->u.set.name);
            v = eval(e->u.set.exp, env);
            return *find(e->u.set.name, env) = v;
        }
    case IFX:
        /* evaluate [[e->u.if]] and return 633d */
        if (istrue(eval(e->u.ifx.cond, env)))
            return eval(e->u.ifx.true, env);
        else
            return eval(e->u.ifx.false, env);
    case WHILEX:
        /* evaluate [[e->u.while]] and return 634a */
        while (istrue(eval(e->u.whilex.cond, env)))
            eval(e->u.whilex.body, env);
        return falsev;
    case BEGIN:
        /* evaluate [[e->u.begin]] and return 634b */
        {
            Explist el;
            Value v = falsev;
            for (el = e->u.begin; el; el = el->tl)
                v = eval(el->hd, env);
            return v;
        }
    case LETX:
        /* evaluate let expression and return 632b */
        {
            Value rv;

            pushroot(mkEnvroot(&env));
            switch (e->u.letx.let) {
            case LET:
                if (duplicatename(e->u.letx.nl) != NULL)
                    error("bound name %n appears twice in let", duplicatename(e
                                                                  ->u.letx.nl));
                /* extend [[env]] by simultaneously binding [[el]] to [[nl]] 633
                                                                            a */
                {
                    Valuelist vl = evallist(e->u.letx.el, env);
                    pushroot(mkValuelistroot(&vl));
                    env = bindalloclist(e->u.letx.nl, vl, env);
                    poproot(mkValuelistroot(&vl));
                }
                break;
            case LETSTAR:
                /* extend [[env]] by sequentially binding [[el]] to [[nl]] 633b
                                                                              */
                {
                    Namelist nl;
                    Explist el;

                    for (nl = e->u.letx.nl, el = e->u.letx.el; nl && el; nl = nl
                                                              ->tl, el = el->tl)
                        env = bindalloc(nl->hd, eval(el->hd, env), env);
                    assert(nl == NULL && el == NULL);
                }
                break;
            case LETREC:
                if (duplicatename(e->u.letx.nl) != NULL)
                    error("bound name %n appears twice in letrec", duplicatename
                                                                (e->u.letx.nl));
                /* extend [[env]] by recursively binding [[el]] to [[nl]] 633c
                                                                              */
                {
                    Namelist nl;
                    Valuelist vl;

                    for (nl = e->u.letx.nl; nl; nl = nl->tl)
                        env = bindalloc(nl->hd, mkNil(), env);

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

            rv = eval(e->u.letx.body, env);
            poproot(mkEnvroot(&env));
            return rv;
        }
    case LAMBDAX:
        /* evaluate [[e->u.lambdax]] and return 630b */
        if (duplicatename(e->u.lambdax.formals) != NULL)
            error("formal parameter %n appears twice in lambda",
                  duplicatename(e->u.lambdax.formals));
        return mkClosure(e->u.lambdax, env);
    case APPLY:
        /* evaluate [[e->u.apply]] and return 631a */
        {
            Value rv;
            Value f = eval(e->u.apply.fn, env);
            Valuelist vl;

            pushroot(mkStackvalueroot(&f));
            vl = evallist(e->u.apply.actuals, env);
            pushroot(mkValuelistroot(&vl));

            switch (f.alt) {
            case PRIMITIVE:
                /* apply [[f.u.primitive]], storing the result in [[rv]] 631b */
                rv = f.u.primitive.function(e, f.u.primitive.tag, vl);
                break;
            case CLOSURE:
                /* apply [[f.u.closure]], storing the result in [[rv]] 631c */
                {
                    Env env;
                    Namelist nl = f.u.closure.lambda.formals;
                    checkargc(e, lengthNL(nl), lengthVL(vl));

                    env = bindalloclist(nl, vl, f.u.closure.env);
                    pushroot(mkEnvroot(&env));
                    rv = eval(f.u.closure.lambda.body, env);
                    poproot(mkEnvroot(&env));
                }
                break;
            default:
                error("%e evaluates to non-function %v in %e", e->u.apply.fn, f,
                                                                             e);
            }
            poproot(mkValuelistroot(&vl));
            poproot(mkStackvalueroot(&f));
            return rv;
        }
    }
    assert(0);
    return falsev;
}
/* eval.c 632a */
static Valuelist evallist(Explist el, Env env) {
    if (el == NULL) {
        return NULL;
    } else {
        Value v = eval(el->hd, env);      /* enforce uScheme's order of
                                                                   evaluation */
        Valuelist rv;
        pushroot(mkStackvalueroot(&v));
        rv = mkVL(v, evallist(el->tl, env));
        poproot(mkStackvalueroot(&v));
        return rv;
    }
}
/* eval.c 634c */
Env evaldef(Def d, Env env, int echo) {
    switch (d->alt) {
    case VAL:
        /* evaluate [[val]] binding and return new environment 635a */
        {
            Value v;

            if (find(d->u.val.name, env) == NULL)
                env = bindalloc(d->u.val.name, mkNil(), env);
            pushroot(mkEnvroot(&env));
            v = eval(d->u.val.exp, env);
            poproot(mkEnvroot(&env));
            *find(d->u.val.name, env) = v;
            if (echo) {
                if (d->u.val.exp->alt == LAMBDAX)
                    print("%n\n", d->u.val.name);
                else
                    print("%v\n", v);
            }
            return env;
        }
    case DEFINE:
        /* evaluate function definition and return new environment 635b */
        if (duplicatename(d->u.define.lambda.formals) != NULL)
            error(
               "formal parameter %n appears twice in definition of function %n",
                  duplicatename(d->u.define.lambda.formals), d->u.define.name);
        return evaldef(mkVal(d->u.define.name, mkLambdax(d->u.define.lambda)),
                                                                     env, echo);
    case EXP:
        /* evaluate expression, store the result in [[it]], and return new
                                                             environment 634d */
        {
            Value v = eval(d->u.exp, env);
            Value *itloc = find(strtoname("it"), env);
            if (echo)
                print("%v\n", v);
            if (itloc == NULL) {
                pushroot(mkStackvalueroot(&v));
                env = bindalloc(strtoname("it"), v, env);
                poproot(mkStackvalueroot(&v));
                return env;
            } else {
                *itloc = v;
                return env;
            }
        }
    case USE:
        /* read in a file and return new environment 635c */
        {
            FILE *fin;
            const char *filename;

            filename = nametostr(d->u.use);
            fin = fopen(filename, "r");
            if (fin == NULL)
                error("cannot open file \"%s\"", filename);
            pushroot(mkEnvroot(&env));
            readevalprint(defreader(filereader(filename, fin), 0), &env, 1);
            poproot(mkEnvroot(&env));
            fclose(fin);
            return env;
        }
    default:
        assert(0);
        return NULL;
    }
}
/* eval.c 636a */
void readevalprint(Defreader reader, Env *envp, int echo)
{
    Def d;

    pushroot(mkDefroot(&d));
    d = NULL; /* don't allow garbage on stack during first call to [[readdef]]
                                                                              */
    while ((d = readdef(reader)))
        *envp = evaldef(d, *envp, echo);
    poproot(mkDefroot(&d));
}
