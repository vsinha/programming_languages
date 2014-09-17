/*
 * Parsing
 * 
 * This is really not interesting.
 * 
 * <parse.c>=
 */
#include "all.h"

/*
 * The [[getnamelist]] function turns a [[Parlist]] that
 * is a list of names into a [[Namelist]], calling
 * [[error]] if the [[Parlist]] contains any sublists.
 * The passed [[Par]] parameter is only for printing a
 * good error message.
 * <parse.c declarations>=
 */
Namelist getnamelist(Par p, Parlist pl);
/*
 * Now we can move on to parsing [[Exp]]s. The
 * [[parselist]] helper function parses a list of
 * [[Par]] expressions and calls [[parseexp]] repeatedly
 * to return a list of [[Exp]]s.
 * <parse.c declarations>=
 */
Explist parselist(Parlist);
/*
 * <parse.c declarations>=
 */
Exp parseexp(Par);
/*
 * Function [[parseletbindings]] adds bindings to a let
 * expression.
 * <parse.c declarations>=
 */
static void parseletbindings(Par p, Parlist bindings, Exp letexp);
/*
 * <parse.c declarations>=
 */
Value parsesx(Par p);
/*
 * <parse.c>=
 */
Def parse(Par p) {
    switch (p->alt) {
    case ATOM:
        /*
         * If we have a name, we treat it as an expression.
         * <parse ATOM and return>=
         */
        return mkExp(parseexp(p));
    case LIST:
        /*
         * If we have a list, we need to look for [[define]],
         * [[val]], and [[use]].
         * <parse LIST and return>=
         */
        {
            Parlist pl = p->u.list;

            if (pl == NULL)
                error("%p: empty list", p);
            if (nthPL(pl, 0)->alt == ATOM) {
                Name first = nthPL(pl, 0)->u.atom;
                if (first == strtoname("define")) {
                    /*
                     * Parsing the toplevel expressions requires checking
                     * the argument counts and then parsing the subpieces.
                     * <parse define and return>=
                     */
                    Name name;
                    Lambda l;

                    if (lengthPL(pl) != 4 || nthPL(pl, 1)->alt != ATOM || nthPL(
                                                            pl, 2)->alt != LIST)
                        error("%p: usage: (define fun (args) body)", p);

                    name      = nthPL(pl, 1)->u.atom;
                    l.formals = getnamelist(p, nthPL(pl, 2)->u.list);
                    l.body    = parseexp(nthPL(pl, 3));
                    return      mkDefine(name, l);
                }
                if (first == strtoname("val")) {
                    /*
                     * <parse val and return>=
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
                     * <parse use and return>=
                     */
                    if (lengthPL(pl) != 2 || nthPL(pl, 1)->alt != ATOM)
                        error("%p: usage: (use filename)", p);

                    return mkUse(nthPL(pl, 1)->u.atom);
                }
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
Namelist getnamelist(Par p, Parlist pl) {
    if (pl == NULL)
        return NULL;
    if (pl->hd->alt != ATOM)
        error("%p: formal parameter list contains %p, which is not a name", p,
                                                                        pl->hd);
    return mkNL(pl->hd->u.atom, getnamelist(p, pl->tl));
}
/*
 * <parse.c>=
 */
Explist parselist(Parlist pl) {
    Exp e;

    if (pl == NULL)
        return NULL;

    e = parseexp(pl->hd);
    return mkEL(e, parselist(pl->tl));
}
/*
 * <parse.c>=
 */
Exp parseexp(Par p) {
    switch (p->alt) {
    case ATOM:
        /*
         * To parse an atom, we need to check whether it is a
         * boolean or a number. Otherwise it is a variable.
         * <parseexp [[ATOM]] and return>=
         */
        {
            Name n = p->u.atom;
            const char *s; /* string form of n */
            char *t;       /* nondigits in s, if any */
            long l;        /* number represented by s, if any */

            if (n == strtoname("#t"))
                return mkLiteral(truev);
            else if (n == strtoname("#f"))
                return mkLiteral(falsev);

            s = nametostr(n);
            l = strtol(s, &t, 10);
            if (*t == '\0' && *s != '\0') /* all the characters in s are digits
                                                                      base 10 */
                return mkLiteral(mkNum(l));
            else
                return mkVar(n);
        }
    case LIST:
        /*
         * If we have a list, we need to see if the first
         * element is a special name. In anticipation of code we
         * need for Chapter [->], we put the parsed expression
         * into [[rv]] (for ``return value'') instead of
         * returning it directly. We treat [[lambda]], the let
         * family, and [[quote]] specially, because their
         * arguments are not always expressions. For other
         * phrases, the arguments are almost always expressions,
         * so we call [[parselist]]. This means we cheat a bit
         * on [[set]], but so be it.
         * <parseexp [[LIST]] and return>=
         */
        {
            Parlist pl;                /* parenthesized list we are parsing */
            Name first;                /* first element, as a name (or NULL if
                                                                    not name) */
            Explist el;                /* remaining elements, as expressions */
            Exp rv;                    /* result of parsing */

            pl = p->u.list;
            if (pl == NULL)
                error("%p: empty list in input", p);

            first = pl->hd->alt == ATOM ? pl->hd->u.atom : NULL;
            if (first == strtoname("lambda")) {
                /*
                 * <parseexp [[lambda]] and put the result in [[rv]]>=
                 */
                Par q;

                if (lengthPL(pl->tl) != 2)
                    error("%p: usage: (lambda (formals) exp)", p);
                q = nthPL(pl->tl, 0);
                if (q->alt != LIST)
                    error("%p: usage: (lambda (formals) exp)", p);
                rv = mkLambdax(mkLambda(getnamelist(p, q->u.list), parseexp(
                                                            nthPL(pl->tl, 1))));
            } else if (first == strtoname("let")
                   ||  first == strtoname("let*")
                   ||  first == strtoname("letrec")) {
                /*
                 * <parseexp let and put the result in [[rv]]>=
                 */
                Letkeyword letword;
                Par letbindings;

                if (first == strtoname("let"))
                    letword = LET;
                else if (first == strtoname("let*"))
                    letword = LETSTAR;
                else if (first == strtoname("letrec"))
                    letword = LETREC;
                else
                    assert(0);

                if (lengthPL(pl->tl) != 2)
                    error("%p: usage: (%n (letlist) exp)", p, first);

                letbindings = nthPL(pl->tl, 0);
                if (letbindings->alt != LIST)
                    error("%p: usage: (%n (letlist) exp)", p, first);

                rv = mkLetx(letword, NULL, NULL, parseexp(nthPL(pl->tl, 1)));

                parseletbindings(p, letbindings->u.list, rv);
            } else if (first == strtoname("quote")) {
                /*
                 * <parseexp [[quote]] and put the result in [[rv]]>=
                 */
                {
                    if (lengthPL(pl) != 2)
                        error("%p: quote needs exactly one argument", p);
                    rv = mkLiteral(parsesx(nthPL(pl, 1)));
                }
            } else {
                el = parselist(pl->tl);
                if (first == strtoname("begin")) {
                    /*
                     * A [[begin]] statement can have any number of
                     * parameters.
                     * <parseexp [[begin]] and put the result in [[rv]]>=
                     */
                    rv = mkBegin(el);
                } else if (first == strtoname("if")) {
                    /*
                     * An [[if]] statement needs three parameters.
                     * <parseexp [[if]] and put the result in [[rv]]>=
                     */
                    if (lengthEL(el) != 3)
                        error("%p: usage: (if cond true false)", p);
                    rv = mkIfx(nthEL(el, 0), nthEL(el, 1), nthEL(el, 2));
                } else if (first == strtoname("set")) {
                    /*
                     * A [[set]] statement requires a variable and a value.
                     * <parseexp [[set]] and put the result in [[rv]]>=
                     */
                    if (lengthEL(el) != 2)
                        error("%p: usage: (set var exp)", p);
                    if (nthEL(el, 0)->alt != VAR)
                        error("%p: set needs variable as first param", p);
                    rv = mkSet(nthEL(el, 0)->u.var, nthEL(el, 1));
                } else if (first == strtoname("while")) {
                    /*
                     * A [[while]] loop needs two.
                     * <parseexp [[while]] and put the result in [[rv]]>=
                     */
                    if (lengthEL(el) != 2)
                        error("%p: usage: (while cond body)", p);
                    rv = mkWhilex(nthEL(el, 0), nthEL(el, 1));
                } else {
                   /*
                    * Parsing function application.
                    * <parseexp application and put the result in [[rv]]>=
                    */
                   rv = mkApply(parseexp(pl->hd), el);
                }
            }
            return rv;
        }
    default:
        assert(0);
        return NULL;
    }
}
/*
 * <parse.c>=
 */
static void parseletbindings(Par p, Parlist bindings, Exp letexp) {
    if (bindings) {
        Par t = bindings->hd;
        Name n;  /* name bound in t (if t is well formed) */
        Exp e;   /* expression on RHS of t (if t is well formed) */
        parseletbindings(p, bindings->tl, letexp);
        if (t->alt != LIST || lengthPL(t->u.list) != 2 
        ||  nthPL(t->u.list, 0)->alt != ATOM)
            error("%p: usage: (letX (letlist) exp)", p);
        n = nthPL(t->u.list, 0)->u.atom;
        e = parseexp(nthPL(t->u.list, 1));
        letexp->u.letx.nl = mkNL(n, letexp->u.letx.nl);
        letexp->u.letx.el = mkEL(e, letexp->u.letx.el);
    }
}
/*
 * <parse.c>=
 */
Value parsesx(Par p) {
    switch (p->alt) {
    case ATOM:
        {
            Name n        = p->u.atom;
            const char *s = nametostr(n);
            long l;            /* value of digits in s, if any */
            char *t;           /* first nondigit in s */

            l = strtol(s, &t, 10);
            if (*t == '\0' && *s != '\0')  /* s is all digits */
                return mkNum(l);
            else if (strcmp(s, "#t") == 0)
                return truev;
            else if (strcmp(s, "#f") == 0)
                return falsev;
            else if (strcmp(s, ".") == 0)
                error("this interpreter cannot handle . in quoted S-expressions"
                                                                              );
            else
                return mkSym(n);
        }
    case LIST:
        /*
         * <parsesx [[LIST]] and return>=
         */
        if (p->u.list == NULL)
            return mkNil();
        else
            return mkPair(allocate(parsesx(p->u.list->hd)),
                          allocate(parsesx(mkList(p->u.list->tl))));
    }
    assert(0);
    return falsev;
}
/*
 * Now we can assemble [[readtop]]. We keep a list of
 * read but not yet parsed [[Par]]s in [[tr->pl]].
 * <parse.c>=
 */
struct Defreader {
    int doprompt;  /* whether to prompt at each definition */
    Reader r;      /* underlying reader of Pars */
    Parlist pl;    /* Pars read but not yet parsed */
};
/*
 * <parse.c>=
 */
Def readdef(Defreader dr) {
    Par p;

    if (dr->pl == NULL) {
        dr->pl = readparlist(dr->r, 1, dr->doprompt);
        if (dr->pl == NULL) 
            return NULL;
    }

    p = dr->pl->hd;
    dr->pl = dr->pl->tl;
    return parse(p);
}
/*
 * <parse.c>=
 */
Defreader defreader(Reader r, int doprompt) {
    Defreader dr;

    dr = malloc(sizeof(*dr));
    assert(dr != NULL);

    dr->r        = r;
    dr->doprompt = doprompt;
    dr->pl       = NULL;
    return dr;
}
