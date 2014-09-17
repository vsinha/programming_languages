/*
 * Input Readers
 * 
 * <read.c>=
 */
#include "all.h"
/*
 * The reader creators are simple.
 * <read.c>=
 */
Reader stringreader(const char *stringname, const char *s) {
    Reader r = calloc(1, sizeof(*r));
    assert(r);
    r->readername = stringname;
    r->s = s;
    return r;
}
/*
 * <read.c>=
 */
Reader filereader(const char *filename, FILE *fin) {
    Reader r = calloc(1, sizeof(*r));
    assert(r);
    r->readername = filename;
    r->fin = fin;
    return r;
}
/*
 * Function [[readline]] returns a pointer to the next
 * line from the input, which is held in a buffer that
 * is reused on subsequent calls. Function [[growbuf]]
 * makes sure the buffer is at least [[n]] bytes long.
 * <read.c>=
 */
static void growbuf(Reader r, int n) {
    if (r->nbuf < n) {
        r->buf = realloc(r->buf, n);
        assert(r->buf != NULL);
        r->nbuf = n;
    }
}
/*
 * We cook [[readline]] to print out the line read if it
 * begins with the string [[;#]]. This string is a
 * special comment that helps us test the chunks marked
 * [[]].
 * <read.c>=
 */
char* readline(Reader r, char *prompt) {
    if (prompt)
        print("%s", prompt);

    r->line++;
    if (r->fin)
        /*
         * Returning the next line from a file requires us to
         * continually call [[fgets]] until we get a newline
         * character at the end of the returned string.
         * <set [[r->buf]] to next line from file, or return [[NULL]] if lines
                                                                 are exhausted>=
         */
        {
            int n;

            for (n = 0; n == 0 || r->buf[n-1] != '\n'; n = strlen(r->buf)) {
                growbuf(r, n+512);
                if (fgets(r->buf+n, 512, r->fin) == NULL)
                    break;
            }
            if (n == 0)
                return NULL;
            if (r->buf[n-1] == '\n')
                r->buf[n-1] = '\0';
        }
    else if (r->s)
        /*
         * To return the next line in a string, we need to find
         * it and update the pointer.
         * <set [[r->buf]] to next line from string, or return [[NULL]] if lines
                                                                 are exhausted>=
         */
        {
            const char *p;
            int len;

            if ((p = strchr(r->s, '\n')) == NULL)
                return NULL;

            p++;

            len = p - r->s;
            growbuf(r, len);
            strncpy(r->buf, r->s, len);
            r->buf[len-1] = '\0';   /* no newline */

            r->s = p;
        }
    else
        assert(0);

    if (r->buf[0] == ';' && r->buf[1] == '#')
        print("%s\n", r->buf);

    return r->buf;
}
