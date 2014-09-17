/*
 * Implementation of the evaluator
 * 
 * [*]
 * <eval.c>=
 */
#include "all.h"

/*
 * As in Impcore's interpreter, [[evallist]] evaluates a
 * list of arguments in turn, returning a list of
 * values.
 * <eval.c declarations>=
 */
static Valuelist evallist(Explist el, Env env);
/*
 * As in Impcore, the evaluator is still a [[switch]]:
 * <eval.c>=
 */
Value eval(Exp e, Env env) {
    checkoverflow(1000000 * sizeof(char *)); /* OMIT */
    switch (e->alt) {
    case LITERAL:
        /*
         * Literals
         * 
         * As in Impcore, literals evaluate to themselves.
         * <evaluate [[e->u.literal]] and return the result>=
         */
        return e->u.literal;
    case VAR:   
        /*
         * Variables
         * 
         * Variable lookup and assignment are simpler than in
         * Impcore, because we have only one rule each. We
         * implement rho(x) by find(x, rho), we implement sigma
         * (l) by [[*]]l, and we update sigma(l) by assigning to
         * [[*]]l. [*]
         * <evaluate [[e->u.var]] and return the result>=
         */
        if (find(e->u.var, env) == NULL)
            error("variable %n not found", e->u.var);
        return *find(e->u.var, env);
    case SET:
        /*
         * [*] [*]
         * <evaluate [[e->u.set]] and return the result>=
         */
        if (find(e->u.set.name, env) == NULL)
            error("set unbound variable %n", e->u.set.name);
        return *find(e->u.set.name, env) = eval(e->u.set.exp, env);
    case IFX:
        /*
         * Conditional, iteration, and sequence
         * 
         * The implementations of the control-flow operations
         * are very much as in Impcore. We don't bother
         * repeating the operational semantics.
         * <evaluate [[e->u.ifx]] and return the result>=
         */
        if (istrue(eval(e->u.ifx.cond, env)))
            return eval(e->u.ifx.true, env);
        else
            return eval(e->u.ifx.false, env);
    case WHILEX:
        /*
         * <evaluate [[e->u.whilex]] and return the result>=
         */
        while (istrue(eval(e->u.whilex.cond, env)))
            eval(e->u.whilex.body, env);
        return falsev;
    case BEGIN:
        /*
         * <evaluate [[e->u.begin]] and return the result>=
         */
        {
            Explist el;
            Value v = falsev;
            for (el = e->u.begin; el; el = el->tl)
                v = eval(el->hd, env);
            return v;
        }
    case APPLY:
        /*
         * We handle application of primitives separately from
         * application of closures.
         * 
         * <evaluate [[e->u.apply]] and return the result>=
         */
        {
            Value     f  = eval    (e->u.apply.fn,      env);
            Valuelist vl = evallist(e->u.apply.actuals, env);

            switch (f.alt) {
            case PRIMITIVE:
                /*
                 * Applying a primitive is simpler than in our Impcore
                 * interpreter because we represent primitives by
                 * function pointers and tags. The tag is passed to the
                 * function, along with the arguments ([[vl]]), plus the
                 * abstract syntax [[e]], which is used in error
                 * messages.
                 * <apply [[f.u.primitive]] to [[vl]] and return the result>=
                 */
                return f.u.primitive.function(e, f.u.primitive.tag, vl);
            case CLOSURE:
                /*
                 * To apply a closure, we extend the closure's
                 * environment (rho_c in the operational semantics) with
                 * the bindings for the formal variables and then
                 * evaluate the body in that environment.
                 * <apply [[f.u.closure]] to [[vl]] and return the result>=
                 */
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
        /*
         * Let, let*, and letrec
         * 
         * Each expression in the [[let]] family uses its
         * internal names and expressions to create a new
         * environment, then evaluates the body in that
         * environment. The rules for creating the environment
         * depend on the keyword.
         * <evaluate [[e->u.letx]] and return the result>=
         */
        switch (e->u.letx.let) {
        case LET:
            /*
             * <if [[e->u.letx.nl]] contains a duplicate, complain of error in
                                                                       [[let]]>=
             */
            if (duplicatename(e->u.letx.nl) != NULL)
                error("bound name %n appears twice in let", duplicatename(e->
                                                                    u.letx.nl));
            /*
             * A \xlet expression evaluates the expressions to be
             * bound, then binds them all at once. The functions
             * [[evallist]] and [[bindalloclist]] do all the work.
             * <extend [[env]] by simultaneously binding [[el]] to [[nl]]>=
             */
            env = bindalloclist(e->u.letx.nl, evallist(e->u.letx.el, env), env);
            break;
        case LETSTAR:
            /*
             * A \xletstar expression binds a new name as each
             * expression is evaluated.
             * 
             * <extend [[env]] by sequentially binding [[el]] to [[nl]]>=
             */
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
            /*
             * <if [[e->u.letx.nl]] contains a duplicate, complain of error in
                                                                    [[letrec]]>=
             */
            if (duplicatename(e->u.letx.nl) != NULL)
                error("bound name %n appears twice in letrec", duplicatename(e->
                                                                    u.letx.nl));
            /*
             * Finally, \xletrec must bind each name to a location
             * before evaluating any of the expressions. The initial
             * contents of the new locations are unspecified. To be
             * faithful to the semantics, we compute all the values
             * before storing any of them.
             * <extend [[env]] by recursively binding [[el]] to [[nl]]>=
             */
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
        /*
         * Closures and function application
         * 
         * Wrapping a closure is simple; we need only to check
         * for duplicate names.
         * <evaluate [[e->u.lambdax]] and return the result>=
         */
        /*
         * Error checking
         * 
         * Here are a few bits of error checking that were
         * omitted from Chapter [->].
         * <if [[e->u.lambdax.formals]] contains a duplicate, call [[error]]>=
         */
        if (duplicatename(e->u.lambdax.formals) != NULL)
            error("formal parameter %n appears twice in lambda",
                  duplicatename(e->u.lambdax.formals));
        return mkClosure(e->u.lambdax, env);
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
        return mkVL(v, evallist(el->tl, env));
    }
}
