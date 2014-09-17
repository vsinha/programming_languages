/*
 * Lexical Analysis
 * 
 * The implementation of lexical analysis is not central
 * to this book; it can be skipped on first and
 * subsequent readings.
 * <lex.c>=
 */
#include "all.h"
#include <ctype.h>
/*
 * To parse input, we use helper routines that take a
 * reference to a string pointer and advance the
 * pointer, returning an object corresponding to the
 * data read.
 * 
 * Function [[readname]] reads the next name from the
 * input string. The [[quote]] flag controls whether a
 * single quote ([[']]) is treated as a special
 * token-breaking character like a parenthesis. Function
 * [[strntoname]] returns the name that corresponds to
 * the first [[n]] characters of a string.
 * <lex.c>=
 */
static Name strntoname(char *s, int n) {
    char *t = malloc(n + 1);
    assert(t != NULL);
    strncpy(t, s, n);
    t[n] = '\0';
    return strtoname(t);
}
/*
 * <lex.c>=
 */
static int isdelim(char c, int quote) {
    if (quote && c == '\'')
        return 1;

    return c == '\0' || c == '(' || c == ')' || c == ';' || isspace(c);
}
/*
 * <lex.c>=
 */
static Name readname(char **ps, int quote) {
    char *p, *q;

    p = *ps;
    for (q = p; !isdelim(*q, quote); q++)
        ;
    *ps = q;
    return strntoname(p, q - p);
}
/*
 * Function [[readpar]] uses [[readname]] to read the
 * next (possibly parenthesized) expression from the
 * input. Function [[skipspace]] advances the [[ps]]
 * pointer over any initial whitespace. The argument to
 * [[isspace]] is required to be unsigned.
 * <lex.c>=
 */
static void skipspace(char **ps) {
    while (isspace((unsigned char)**ps))
        (*ps)++;
}
/*
 * <lex.c>=
 */
enum {
    More       = 1 << 0,
    Quote      = 1 << 1,
    Rightparen = 1 << 2
};
static Par readpar(char **ps, Reader r, int flag, char *moreprompt) {
    if (*ps == NULL)
        return NULL;

    skipspace(ps);

    switch (**ps) {
    case '\0':
    case ';':
        /*
         * If we encounter the end of a line before finding an
         * expression, the result is determined by the [[More]]
         * flag. If it is set, we read a new line and keep
         * going. Otherwise we return [[NULL]] and set [[*ps]]
         * to [[NULL]] to indicate the end of the line.
         * <readpar end of line and return>=
         */
        if ((flag & More) && (*ps = readline(r, moreprompt)) != NULL)
            return readpar(ps, r, flag, moreprompt);
        *ps = NULL;
        return NULL;
    case ')':
        /*
         * When we're not expecting one, a right parenthesis is
         * a fatal error; if we are expecting one, we return
         * NULL but leave [[*ps]] pointing at the parenthesis.
         * <readpar right parenthesis and return>=
         */
        if ((flag & Rightparen) == 0)
            error("unexpected right parenthesis in %s, line %d", r->readername,
                                                                       r->line);
        return NULL;
    case '(':
        /*
         * If we see a left parenthesis, we read tokens until we
         * get a right parenthesis, adding them to the end of a
         * list.
         * <readpar left parenthesis and return>=
         */
        {
            Par p = mkList(NULL);
            Parlist *ppl =&p->u.list;
            Par q;  /* next par read in, to be accumulated into p */

            (*ps)++;
            while ((q = readpar(ps, r, flag | More | Rightparen, moreprompt))) {
                *ppl = mkPL(q, NULL);
                ppl  = &(*ppl)->tl;
            }
            if (*ps == NULL)
                error("premature end of file reading list (missing right paren)"
                                                                              );

            assert(**ps == ')');
            (*ps)++;    /* past right parenthesis */

            return p;
        }
    default:
        if ((flag & Quote) && **ps == '\'') {
            /*
             * If we are lexing a language that uses a [[']]
             * operator, when we see a [[']], we read the next
             * [[Par]] (say [[x]]) and then return [[(quote x)]].
             * <readpar quoted expression and return>=
             */
            {
                Par p;

                (*ps)++;
                p = readpar(ps, r, More|Quote, moreprompt);
                return mkList(mkPL(mkAtom(strtoname("quote")), mkPL(p, NULL)));
            }
        } else {
            /*
             * Names are easy.
             * <readpar name and return>=
             */
            return mkAtom(readname(ps, flag & Quote));
        }
    }   
}
/*
 * Function [[readparlist]] reads [[Par]] expressions
 * until an end of expression and an end of line
 * coincide; it returns the list of expressions read.
 * The strings used as primary and secondary prompts are
 * also buried instead [[readparlist]].[*]
 * <lex.c>=
 */
Parlist readparlist(Reader r, int doquote, int doprompt) {
    char *s;
    Par p;
    Parlist pl = NULL;
    Parlist *ppl = &pl;

    while (pl == NULL) {
        if ((s = readline(r, doprompt ? "-> " : "")) == NULL)
            return NULL;

        while ((p = readpar(&s, r, doquote ? Quote : 0, doprompt ? "   " : "")))
                                                                               {
            *ppl = mkPL(p, NULL);
            ppl  = &(*ppl)->tl;
        }
    }
    return pl;
}
/*
 * <lex.c>=
 */
void printpar(FILE *output, va_list_box *box) {
    Par p = va_arg(box->ap, Par);
    if (p == NULL) {
        fprint(output, "<null>");
        return;
    }

    switch (p->alt){
    case ATOM:
        fprint(output, "%n", p->u.atom);
        break;
    case LIST:
        fprint(output, "(%P)", p->u.list);
        break;
    }
}
/*
 * [[
 * parse.c]]: Parser
 * 
 * [*]
 */

