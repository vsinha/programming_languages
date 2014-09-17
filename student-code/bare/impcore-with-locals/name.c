/* name.c 46d */
#include "all.h"

struct Name {
    const char *s;
};
/* name.c 47a */
const char* nametostr(Name n) {
    assert(n != NULL);
    return n->s;
}
/* name.c 47b */
Name strtoname(const char *s) {
    static Namelist names;
    Namelist nl;

    assert(s != NULL);
    for (nl=names; nl; nl=nl->tl)
        if (strcmp(s, nl->hd->s) == 0)
            return nl->hd;

    /* allocate a new name, add it to [[names]], and return it 47c */
    {
      Name n = malloc(sizeof(*n));
      assert(n != NULL);
      n->s = malloc(strlen(s) + 1);
      assert(n->s != NULL);
      strcpy((char*)n->s, s);
      names = mkNL(n, names);
      return n;
    }
}
/* name.c 47d */
void printname(FILE *output, va_list_box *box) {
    Name n = va_arg(box->ap, Name);
    fputs(n == NULL ? "<null>" : nametostr(n), output);
}
