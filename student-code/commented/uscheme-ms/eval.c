/*
 * The revised micro-Scheme evaluator
 * 
 * The structure is as before.
 * <eval.c>=
 */
#include "all.h"

/*
 * Evallist
 * 
 * In [[evallist]], we push [[v]] before calling
 * [[evallist]] recursively.
 * <eval.c declarations>=
 */
static Valuelist evallist(Explist el, Env env);
/*
 * <eval.c>=
 */
Value eval(Exp e, Env env) {
    checkoverflow(1000000 * sizeof(char *)); /* OMIT */
    switch (e->alt) {
    case LITERAL:
        /*
         * Values and variables
         * 
         * The \rulenameLiteral and \rulenameVar rules don't
         * allocate, so there's no need to worry about roots.
         * <evaluate [[e->u.literal]] and return>=
         */
        return e->u.literal;
    case VAR:   
        /*
         * <evaluate [[e->u.var]] and return>=
         */
        if (find(e->u.var, env) == NULL)
            error("variable %n not found", e->u.var);
        return *find(e->u.var, env);
    case SET:
        /*
         * The \rulenameAssign rule does allocate because it
         * calls [[eval]] to evaluate the right-hand side.
         * Because C does not specify the order of evaluation,
         * we cannot implement [[set]] using the simple
         * assignment we use in chunk [->]. The risk is that the
         * C compiler might call [[find(e->u.set.name, env)]]
         * first. If this happens, the value returned is a
         * pointer to an object allocated on the heap. But
         * calling [[eval]] might trigger a garbage collection,
         * objects on the heap would move, and the assignment
         * would write over the wrong location. We avoid such a
         * disaster by calling [[eval]] first, saving the result
         * in [[v]], and then calling [[find]]. We needn't push 
         * [[v]] on the root stack because [[find]] doesn't
         * allocate.
         * <evaluate [[e->u.set]] and return>=
         */
        {
            Value v;

            if (find(e->u.set.name, env) == NULL)
                error("set unbound variable %n", e->u.set.name);
            v = eval(e->u.set.exp, env);
            return *find(e->u.set.name, env) = v;
        }
    case IFX:
        /*
         * Control flow
         * 
         * For the most part, control flow can ignore the root
         * stack, since there are no intermediate values.
         * <evaluate [[e->u.if]] and return>=
         */
        if (istrue(eval(e->u.ifx.cond, env)))
            return eval(e->u.ifx.true, env);
        else
            return eval(e->u.ifx.false, env);
    case WHILEX:
        /*
         * <evaluate [[e->u.while]] and return>=
         */
        while (istrue(eval(e->u.whilex.cond, env)))
            eval(e->u.whilex.body, env);
        return falsev;
        /*
         * [[
         * Begin]] repeatedly assigns to [[v]], but [[v]] is
         * not a root?at the time we call [[eval]], [[v]] is
         * dead.
         */

    case BEGIN:
        /*
         * <evaluate [[e->u.begin]] and return>=
         */
        {
            Explist el;
            Value v = falsev;
            for (el = e->u.begin; el; el = el->tl)
                v = eval(el->hd, env);
            return v;
        }
    case LETX:
        /*
         * Let, let*, and letrec
         * 
         * The implementations of all let expressions require
         * assigning to [[env]], then evaluating the body with
         * the new [[env]]. By pushing [[ --- env]] on the root
         * stack, we ensure that all the modified versions are
         * visible on the root stack.
         * <evaluate let expression and return>=
         */
        {
            Value rv;

            pushroot(mkEnvroot(&env));
            switch (e->u.letx.let) {
            case LET:
                if (duplicatename(e->u.letx.nl) != NULL)
                    error("bound name %n appears twice in let", duplicatename(e
                                                                  ->u.letx.nl));
                /*
                 * Because [[bindalloclist]] allocates, the tracing
                 * invariant requires that [[vl]] be on the root stack.
                 * <extend [[env]] by simultaneously binding [[el]] to [[nl]]>=
                 */
                {
                    Valuelist vl = evallist(e->u.letx.el, env);
                    pushroot(mkValuelistroot(&vl));
                    env = bindalloclist(e->u.letx.nl, vl, env);
                    poproot(mkValuelistroot(&vl));
                }
                break;
            case LETSTAR:
                /*
                 * In the implementation of [[let*]], you might think
                 * that the result of [[eval(el->hd, env)]] would have
                 * to be on the root stack. But the copy in the caller
                 * is dead [A variable or temporary is \emph{dead} if
                 * its value can't possibly affect any future
                 * computation.] as soon as it is passed to
                 * [[bindalloc]], before any allocation can take place.
                 * When potential roots of category A are passed by
                 * value, it's the callee's responsibility to ensure
                 * that they are on the root stack.
                 * <extend [[env]] by sequentially binding [[el]] to [[nl]]>=
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
                /*
                 * To implement [[letrec]], we have the same risk we had
                 * for [[set]]; in the second loop, we must force a
                 * particular order of evaluation for [[evallist]] and
                 * [[find]]. As before, by calling [[evallist]] first,
                 * we avoid having to manipulate the root stack, because
                 * [[find]] doesn't allocate and [[v]] is dead by the
                 * time we call [[eval]] again.
                 * <extend [[env]] by recursively binding [[el]] to [[nl]]>=
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
        /*
         * Closures and application
         * 
         * Making a closure doesn't allocate, so there's no work
         * to be done.
         * <evaluate [[e->u.lambdax]] and return>=
         */
        if (duplicatename(e->u.lambdax.formals) != NULL)
            error("formal parameter %n appears twice in lambda",
                  duplicatename(e->u.lambdax.formals));
        return mkClosure(e->u.lambdax, env);
    case APPLY:
        /*
         * Both primitive and user-defined functions can
         * allocate, so before we can apply a function, we have
         * to get the function value and the actual parameters
         * on the root stack. To keep pushes and pops together,
         * we save the result of application in the ``return
         * value'' [[rv]]. This technique makes it easy to pop
         * the root stack before returning the answer.
         * <evaluate [[e->u.apply]] and return>=
         */
        {
            Value rv;
            Value f = eval(e->u.apply.fn, env);
            Valuelist vl;

            pushroot(mkStackvalueroot(&f));
            vl = evallist(e->u.apply.actuals, env);
            pushroot(mkValuelistroot(&vl));

            switch (f.alt) {
            case PRIMITIVE:
                /*
                 * We apply primitives exactly as in Chapter [->],
                 * except the result goes into [[rv]] instead of being
                 * returned directly.
                 * <apply [[f.u.primitive]], storing the result in [[rv]]>=
                 */
                rv = f.u.primitive.function(e, f.u.primitive.tag, vl);
                break;
            case CLOSURE:
                /*
                 * The tracing invariant requires that [[env]] be on the
                 * root stack before the call to [[eval]].
                 * <apply [[f.u.closure]], storing the result in [[rv]]>=
                 */
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
/*
 * <eval.c>=
 */
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
/*
 * Definitions
 * 
 * Most of the evaluation of definitions is as in
 * Chapter [->].
 * <eval.c>=
 */
Env evaldef(Def d, Env env, int echo) {
    switch (d->alt) {
    case VAL:
        /*
         * Because [[val]] changes our private copy of [[env]],
         * the tracing invariant requires that before we call
         * [[eval]], we must put [[env]] on the root stack.
         * <evaluate [[val]] binding and return new environment>=
         */
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
        /*
         * The definition we get from [[mkVal]] need not be a
         * root because its components are reachable from [[d]],
         * and according to the tracing invariant, [[d]] is
         * guaranteed to be reachable.
         * <evaluate function definition and return new environment>=
         */
        if (duplicatename(d->u.define.lambda.formals) != NULL)
            error(
               "formal parameter %n appears twice in definition of function %n",
                  duplicatename(d->u.define.lambda.formals), d->u.define.name);
        return evaldef(mkVal(d->u.define.name, mkLambdax(d->u.define.lambda)),
                                                                     env, echo);
    case EXP:
        /*
         * To evaluate a top-level expression, we don't need to
         * do anything special to maintain the tracing
         * invariant.
         * <evaluate expression, store the result in [[it]], and return new
                                                                   environment>=
         */
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
        /*
         * Like [[val]], [[use]] modifies our private copy of
         * [[env]].
         * <read in a file and return new environment>=
         */
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
/*
 * The tracing invariant requires that [[readevalprint]]
 * put [[d]] on the root stack, but it guarantees that
 * [[envp]] is already on the root stack. Because we
 * push [[ --- d]], not [[d]], we needn't pop and push
 * at every assignment.
 * <eval.c>=
 */
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
/*
 * The code above has [[ --- d]] on the root stack even
 * during the call to [[readdef]], when [[d]] is not
 * live. If [[readdef]] triggers a garbage collection,
 * garbage in [[t]] (from quoted lists) won't be
 * reclaimed until the next collection cycle.
 */

