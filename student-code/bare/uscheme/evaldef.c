/* evaldef.c 133d */
#include "all.h"
/* evaldef.c 133e */
Env evaldef(Def d, Env env, int echo) {
    switch (d->alt) {
    case VAL:
        /* evaluate [[val]] binding and return new environment 134a */
        {
            Value v;

            if (find(d->u.val.name, env) == NULL)
                env = bindalloc(d->u.val.name, unspecified(), env);
            v = eval(d->u.val.exp, env);
            *find(d->u.val.name, env) = v;
            if (echo) {
                if (d->u.val.exp->alt == LAMBDAX)
                    print("%n\n", d->u.val.name);
                else
                    print("%v\n", v);
            }
            return env;
        }
    case EXP:
        /* evaluate expression, store the result in [[it]], and return new
                                                             environment 134b */
        {
            Value v = eval(d->u.exp, env);
            Value *itloc = find(strtoname("it"), env);
            if (echo)
                print("%v\n", v);
            if (itloc == NULL) {
                return bindalloc(strtoname("it"), v, env);
            } else {
                *itloc = v;
                return env;
            }
        }
    case DEFINE:
        /* evaluate function definition and return new environment 134c */
        /* if [[d->u.define.lambda.formals]] contains a duplicate, call
                                                               [[error]] 611a */
        if (duplicatename(d->u.define.lambda.formals) != NULL)
            error(
               "formal parameter %n appears twice in definition of function %n",
                  duplicatename(d->u.define.lambda.formals), d->u.define.name);
        return evaldef(mkVal(d->u.define.name, mkLambdax(d->u.define.lambda)),
                       env, echo);
    case USE:
        /* read in a file and return new environment 135a */
        {
            const char *filename = nametostr(d->u.use);
            FILE *fin = fopen(filename, "r");
            if (fin == NULL)
                error("cannot open file \"%s\"", filename);
            readevalprint(defreader(filereader(filename, fin), 0), &env, 1);
            fclose(fin);
            return env;
        }
    default:
        assert(0);
        return NULL;
    }
}
/* evaldef.c 135b */
void readevalprint(Defreader reader, Env *envp, int echo) {
    Def d;

    while ((d = readdef(reader)))
        *envp = evaldef(d, *envp, echo);
}
