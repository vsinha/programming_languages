/*
 * Uninteresting implementations
 * 
 * Of the uninteresting implementations, the extensible
 * printer is undoubtedly the most interesting, even if
 * it is the least relevant to programming languages.
 * 
 * Printing
 * 
 * <print.c>=
 */
#include "all.h"

static Printer *printertab[256];
/*
 * <print.c>=
 */
void installprinter(unsigned char c, Printer *printer) {
    printertab[c] = printer;
}
/*
 * <print.c>=
 */
void fprint(FILE *output, const char *fmt, ...) {
    va_list_box box;

    assert(fmt);
    va_start(box.ap, fmt);
    vprint(output, fmt, &box);
    va_end(box.ap);
    fflush(output);
}
/*
 * <print.c>=
 */
void print(const char *fmt, ...) {
    va_list_box box;

    assert(fmt);
    va_start(box.ap, fmt);
    vprint(stdout, fmt, &box);
    va_end(box.ap);
    fflush(stdout);
}
/*
 * <print.c>=
 */
void vprint(FILE *output, const char *fmt, va_list_box *box) {
    unsigned char *p;
    for (p = (unsigned char*)fmt; *p; p++) {
        if (*p != '%') {
            putc(*p, output);
            continue;
        }
        if (printertab[*++p])
            printertab[*p](output, box);
        else {
            fprintf(output, "*%c*", *p);
            break;
        }
    }
}
/*
 * <print.c>=
 */
void printpercent(FILE *output, va_list_box *box) {
    (void)box;
    putc('%', output);
}
/*
 * <print.c>=
 */
void printstring(FILE *output, va_list_box *box) {
    const char *s = va_arg(box->ap, char*);
    fputs(s == NULL ? "<null>" : s, output);
}
/*
 * <print.c>=
 */
void printdecimal(FILE *output, va_list_box *box) {
    fprintf(output, "%d", va_arg(box->ap, int));
}
