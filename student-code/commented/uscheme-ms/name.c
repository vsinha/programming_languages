/*
 * Each name is associated with a string. We use a very
 * simple representation in which the name simply
 * contains the string.
 * <name.c>=
 */
#include "all.h"

struct Name {
    const char *s;
};
/*
 * Returning the string associated with a name is
 * trivial.
 * <name.c>=
 */
const char* nametostr(Name n) {
    assert(n != NULL);
    return n->s;
}
/*
 * Finding the name associated with a string is harder.
 * We must return the same name for any copy of a string
 * we have seen before. We implement this requirement
 * very simply, by keeping [[names]], a list of all
 * names we have ever returned. A simple linear search
 * gives us the name already associated with [[s]], if
 * any.
 * <name.c>=
 */
Name strtoname(const char *s) {
    static Namelist names;
    Namelist nl;

    assert(s != NULL);
    for (nl=names; nl; nl=nl->tl)
        if (strcmp(s, nl->hd->s) == 0)
            return nl->hd;

    /*
     * If the name is not on the list, we make a new one and
     * add it.
     * <allocate a new name, add it to [[names]], and return it>=
     */
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
/*
 * A faster implementation might use a search tree or a
 * hash table, not a simple list. [cite 
 * hanson:interfaces] shows such an implementation.
 */

/*
 * We print a name by printing its string.
 * <name.c>=
 */
void printname(FILE *output, va_list_box *box) {
    Name n = va_arg(box->ap, Name);
    fputs(n == NULL ? "<null>" : nametostr(n), output);
}
