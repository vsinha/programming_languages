/* parse.c 595c */
#include "all.h"

/* parse.c declarations 596d */
static Namelist getnamelist(Name f, Par p, Parlist pl);
/* parse.c declarations 598a */
static Exp parseexp(Par);
/* parse.c 596a */
static Def parse(Par p) {
    switch (p->alt) {
    case ATOM:
        /* parse [[atom]] and return the result 596b */
        return mkExp(parseexp(p));
    case LIST:
        /* parse [[list]] and return the result 596c */
        {
            Name first;
            Parlist pl = p->u.list;
            if (pl == NULL)
                error("%p: empty list", p);
            if (nthPL(pl, 0)->alt != ATOM)
                error("%p: first item of list not name", p);

            first = nthPL(pl, 0)->u.atom;
             if (first == strtoname("define")) {
                 /* parse [[define]] and return the result */
                 if (lengthPL(pl) != 5 || nthPL(pl, 1)->alt != ATOM || 
                     nthPL(pl, 2)->alt != LIST || nthPL(pl, 3)->alt != LIST)
                     error("%p: usage: (define fun (formals) (locals) body)", p);
               {
                 Name     name    = nthPL(pl, 1)->u.atom;
                 Namelist formals = getnamelist(name, p, nthPL(pl, 2)->u.list);
                 Namelist locals  = getnamelist(name, p, nthPL(pl, 3)->u.list);
                 Exp      body    = parseexp(nthPL(pl, 4));
                 return   mkDefine(name, mkUserfun(formals, locals, body));
               }
             }

            if (first == strtoname("val")) {
                /* parse [[val]] and return the result 597c */
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
                /* parse [[use]] and return the result 597d */
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
/* parse.c 597a */
static Namelist getnamelist(Name f, Par p, Parlist pl) {
    if (pl == NULL)
        return NULL;
    if (pl->hd->alt != ATOM)
        error(
"%p: formal-parameter list of function %n contains something that is not a name"
                                                                        , p, f);
    return mkNL(pl->hd->u.atom, getnamelist(f, p, pl->tl));
}
/* parse.c 597e */
static Explist parselist(Parlist pl) {
    Exp e;

    if (pl == NULL)
        return NULL;

    e = parseexp(pl->hd); /* force pl->hd to be parsed first */
    return mkEL(e, parselist(pl->tl));
}
/* parse.c 598b */
static Exp parseexp(Par p) {
    switch (p->alt) {
    case ATOM:
        /* parseexp [[atom]] and return the result 598c */
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
        /* parseexp [[list]] and return the result 599a */
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
                /* parseexp [[begin]] and return the result 599b */
                return mkBegin(argl);
            } else if (first == strtoname("if")) {
                /* parseexp [[if]] and return the result 599c */
                if (lengthEL(argl) != 3)
                    error("%p: usage: (if cond true false)", p);
                return mkIfx(nthEL(argl, 0), nthEL(argl, 1), nthEL(argl, 2));
            } else if (first == strtoname("set")) {
                /* parseexp [[set]] and return the result 599e */
                if (lengthEL(argl) != 2)
                    error("%p: usage: (set var exp)", p);
                if (nthEL(argl, 0)->alt != VAR)
                    error("%p: set needs variable as first param", p);
                return mkSet(nthEL(argl, 0)->u.var, nthEL(argl, 1));
            } else if (first == strtoname("while")) {
                /* parseexp [[while]] and return the result 599d */
                if (lengthEL(argl) != 2)
                    error("%p: usage: (while cond body)", p);
                return mkWhilex(nthEL(argl, 0), nthEL(argl, 1));
            } else {
                /* parseexp function application and return the result 600a */
                return mkApply(first, argl);
            }
        }
    default:
        assert(0);
        return NULL;
    }
}
/* parse.c 600b */
struct Defreader {
    int doprompt;
    Reader r;
    Parlist pl;
};
/* parse.c 600c */
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
/* parse.c 600d */
Defreader defreader(Reader r, int doprompt) {
    Defreader dr = malloc(sizeof(*dr));
    assert(dr != NULL);
    dr->r        = r;
    dr->doprompt = doprompt;
    dr->pl       = NULL;
    return dr;
}
