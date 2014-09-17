/*
 * <parse.c>=
 */
#include "all.h"

/*
 * The [[getnamelist]] function turns a [[Parlist]] that
 * is a list of names into a [[Namelist]], calling
 * [[error]] if the [[Parlist]] contains any sublists.
 * The [[Par*]] parameter is used only to print a good
 * error message.
 * <parse.c declarations>=
 */
static Namelist getnamelist(Name f, Par p, Parlist pl);
/*
 * Parsing expressions first depends on whether we have
 * a name or a list.
 * <parse.c declarations>=
 */
static Exp parseexp(Par);
/*
 * The parser needs to take concrete syntax, check to
 * see that it is well formed, and produce abstract
 * syntax. It provides the [[readtop]] function.
 * 
 * At the top level, parsing amounts to looking for top
 * level constructs and passing the rest of the work to
 * [[parseexp]], which parses the input into [[Exp]]s.
 * <parse.c>=
 */
static Def parse(Par p) {
    switch (p->alt) {
    case ATOM:
        /*
         * If we have a name, we treat it as an expression.
         * <parse [[atom]] and return the result>=
         */
        return mkExp(parseexp(p));
    case LIST:
        /*
         * If we have a list, we need to look for [[define]],
         * [[val]], and [[use]].
         * <parse [[list]] and return the result>=
         */
        {
            Name first;
            Parlist pl = p->u.list;
            if (pl == NULL)
                error("%p: empty list", p);
            if (nthPL(pl, 0)->alt != ATOM)
                error("%p: first item of list not name", p);

            first = nthPL(pl, 0)->u.atom;
            if (first == strtoname("define")) {
                /*
                 * Parsing the top-level expressions requires checking
                 * the argument counts and then parsing the subpieces.
                 * For function definitions, we could check that formal
                 * parameters have distinct names, but that check is
                 * part of the operational semantics for function
                 * definition.
                 * <parse [[define]] and return the result>=
                 */
                if (lengthPL(pl) != 4 || nthPL(pl, 1)->alt != ATOM || nthPL(pl,
                                                                2)->alt != LIST)
                    error("%p: usage: (define fun (formals) body)", p);

                {
                  Name     name    = nthPL(pl, 1)->u.atom;
                  Namelist formals = getnamelist(name, p, nthPL(pl, 2)->u.list);
                  Exp      body    = parseexp(nthPL(pl, 3));
                  return mkDefine(name, mkUserfun(formals, body));
                }
            }
            if (first == strtoname("val")) {
                /*
                 * <parse [[val]] and return the result>=
                 */
                Exp var, exp;

                if (lengthPL(pl) != 3)
                    error("%p: usage: (val var exp)", p);

                var = parseexp(nthPL(pl, 1));
                if (var->alt != VAR)
                    error("%p: usage: (val var exp) (bad variable)", p);

                exp = parseexp(nthPL(pl, 2));
                return mkVal(var->u.var, exp);
            }
            if (first == strtoname("use")) {
                /*
                 * <parse [[use]] and return the result>=
                 */
                if (lengthPL(pl) != 2 || nthPL(pl, 1)->alt != ATOM)
                    error("%p: usage: (use filename)", p);

                return mkUse(nthPL(pl, 1)->u.atom);
            }
            return mkExp(parseexp(p));
        }
    }
    assert(0);
    return NULL;
}
/*
 * <parse.c>=
 */
static Namelist getnamelist(Name f, Par p, Parlist pl) {
    if (pl == NULL)
        return NULL;
    if (pl->hd->alt != ATOM)
        error(
"%p: formal-parameter list of function %n contains something that is not a name"
                                                                        , p, f);
    return mkNL(pl->hd->u.atom, getnamelist(f, p, pl->tl));
}
/*
 * Now we can move on to parsing [[Exp]]s. The
 * [[parselist]] helper function repeatedly calls
 * [[parseexp]] to parse a list of [[Par]] expressions,
 * eventually returning a list of [[Exp]]s.
 * <parse.c>=
 */
static Explist parselist(Parlist pl) {
    Exp e;

    if (pl == NULL)
        return NULL;

    e = parseexp(pl->hd); /* force pl->hd to be parsed first */
    return mkEL(e, parselist(pl->tl));
}
/*
 * <parse.c>=
 */
static Exp parseexp(Par p) {
    switch (p->alt) {
    case ATOM:
        /*
         * If we have a name, it must be either a literal value
         * or a variable.
         * <parseexp [[atom]] and return the result>=
         */
        {
            const char *s = nametostr(p->u.atom);
            char *t;
            long l = strtol(s, &t, 10);
            if (*t == '\0') /* the number is the whole string */
                return mkLiteral(l);
            else
                return mkVar(p->u.atom);
        }
    case LIST:
        /*
         * If we have a list, we need to look at the first
         * element, which must be a name.
         * <parseexp [[list]] and return the result>=
         */
        {
            Parlist pl;
            Name first;
            Explist argl;

            pl = p->u.list;
            if (pl == NULL)
                error("%p: empty list in input", p);
            if (pl->hd->alt != ATOM)
                error("%p: first item of list not name", p);

            first = pl->hd->u.atom;
            argl  = parselist(pl->tl);
            if (first == strtoname("begin")) {
                /*
                 * A [[begin]] expression can have any number of
                 * parameters.
                 * <parseexp [[begin]] and return the result>=
                 */
                return mkBegin(argl);
            } else if (first == strtoname("if")) {
                /*
                 * An [[if]] expression needs three parameters.
                 * <parseexp [[if]] and return the result>=
                 */
                if (lengthEL(argl) != 3)
                    error("%p: usage: (if cond true false)", p);
                return mkIfx(nthEL(argl, 0), nthEL(argl, 1), nthEL(argl, 2));
            } else if (first == strtoname("set")) {
                /*
                 * A [[set]] expression requires a variable and a value.
                 * <parseexp [[set]] and return the result>=
                 */
                if (lengthEL(argl) != 2)
                    error("%p: usage: (set var exp)", p);
                if (nthEL(argl, 0)->alt != VAR)
                    error("%p: set needs variable as first param", p);
                return mkSet(nthEL(argl, 0)->u.var, nthEL(argl, 1));
            } else if (first == strtoname("while")) {
                /*
                 * A [[while]] loop needs two.
                 * <parseexp [[while]] and return the result>=
                 */
                if (lengthEL(argl) != 2)
                    error("%p: usage: (while cond body)", p);
                return mkWhilex(nthEL(argl, 0), nthEL(argl, 1));
            } else {
                /*
                 * Anything else must be a function application. We
                 * can't check the number of parameters here, because
                 * the function definition might change before
                 * evaluation, or might not be present yet (as occurs,
                 * for example, when defining recursive functions).
                 * <parseexp function application and return the result>=
                 */
                return mkApply(first, argl);
            }
        }
    default:
        assert(0);
        return NULL;
    }
}
/*
 * Now we can assemble [[readtop]]. We keep a list of
 * read but not yet parsed [[Par]]s in [[tr->pl]].
 * <parse.c>=
 */
struct Defreader {
    int doprompt;
    Reader r;
    Parlist pl;
};
/*
 * <parse.c>=
 */
Def readdef(Defreader dr) {
    Par p;

    if (dr->pl == NULL) {
        dr->pl = readparlist(dr->r, 0, dr->doprompt);
        if (dr->pl == NULL) 
            return NULL;
    }

    p      = dr->pl->hd;
    dr->pl = dr->pl->tl;
    return parse(p);
}
/*
 * <parse.c>=
 */
Defreader defreader(Reader r, int doprompt) {
    Defreader dr = malloc(sizeof(*dr));
    assert(dr != NULL);
    dr->r        = r;
    dr->doprompt = doprompt;
    dr->pl       = NULL;
    return dr;
}
