/*
 * The interpreter
 * 
 * [*]
 * 
 * This section presents the code for an interpreter
 * written in C. As in the Impcore interpreter, we break
 * the program into modules with well-defined
 * interfaces. We reuse the name routines, the lexer,
 * the input readers, and the printer from the
 * implementation of Impcore.
 * 
 * Interfaces
 * 
 * As in Impcore, we gather all the interfaces into a
 * single C header file.
 * <{\Tt all.h} for \uscheme>=
 */
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <setjmp.h>
#include <ctype.h>
/*
 * For real implementations, it is convenient to build
 * names from strings. Unlike C strings, names are
 * immutable, and they can be compared using pointer
 * equality.
 * <shared type definitions>=
 */
typedef struct Name *Name;
typedef struct Namelist *Namelist;   /* list of Name */
/*
 * Reading characters
 * 
 * A [[Reader]] encapsulates a source of characters: a
 * string or a file. The [[readline]] function prints a
 * prompt, reads the next line of input from the source,
 * and returns a pointer to the line. The caller needn't
 * worry about how long the line is; [[readline]] always
 * allocates enough memory to hold it. Because
 * [[readline]] reuses the same memory to hold
 * successive lines, it is an unchecked run-time error
 * to retain a pointer returned by [[readline]] after a
 * subsequent call to [[readline]]. A client that needs
 * to save input characters must copy the result of
 * [[readline]] before calling [[readline]] again.
 * <shared type definitions>=
 */
typedef struct Reader *Reader;
/*
 * Reading definitions
 * 
 * A [[Defreader]] encapsulates a source of definitions.
 * The [[readdef]] function returns the next definition.
 * It may also return [[NULL]], if there are no more
 * definitions in the source, or call [[error]] (page 
 * [->]), if there is some problem converting the source
 * to abstract syntax.
 * <shared type definitions>=
 */
typedef struct Defreader *Defreader;
/*
 * If you just want to use the functions, without
 * learning how to extend them, you can use only
 * [[print]] and [[eprint]]?ignore [[vprint]] and the
 * details of [[Printer]] and [[installprinter]] that
 * follow.
 * 
 * An extension to [[print]] or [[eprint]] knows how to
 * print one type of C value, like an Impcore expression
 * or value. Such a function has type [[Printer]];
 * a printer consumes and writes one argument from a
 * [[va_list_box]], which holds a list of arguments. [*]
 * <shared type definitions>=
 */
/*
 * Extensible printers are popular with sophisticated
 * C programmers; Hanson (1996, Chapter 14) presents an
 * especially well-crafted example. Unfortunately, some
 * widely used compilers make the construction of
 * extensible printers more difficult than necessary.
 * In particular, not all versions of the GNU C compiler
 * work correctly when values of type [[va_list]] are
 * passed as arguments on the AMD64 platform. [Library
 * functions such as [[vfprintf]] itself are
 * grandfathered; only users cannot write functions that
 * take [[va_list]] arguments. Feh.] \codeindex
 * va-list-box@va_list_box A workaround for this problem
 * is to place the [[va_list]] in a structure and pass a
 * pointer to the structure:
 * <definition of [[va_list_box]]>=
 */
typedef struct va_list_box {
  va_list ap;
} va_list_box;
/*
 * If you are not accustomed to variadic functions and
 * [[stdarg.h]], you may wish to consult Sections
 * 7.2 and 7.3 of \citeNNkernighan:c:2.
 */

typedef void Printer(FILE *output, va_list_box*);
/*
 * <shared type definitions>=
 */
typedef struct Parlist *Parlist; /* list of Par */
/*
 * <shared type definitions>=
 */
typedef struct Par *Par;
typedef enum { ATOM, LIST } Paralt; 
/*
 * <type definitions for \uscheme>=
 */
typedef struct Lambda Lambda; 
typedef struct Value Value;
typedef enum { NIL, BOOL, NUM, SYM, PAIR, CLOSURE, PRIMITIVE } Valuealt;

/*
 * <type definitions for \uscheme>=
 */
typedef struct Def *Def;
typedef enum { VAL, EXP, DEFINE, USE } Defalt; 
typedef struct Exp *Exp;
typedef enum {
    LITERAL, VAR, SET, IFX, WHILEX, BEGIN, APPLY, LETX, LAMBDAX
} Expalt;

/*
 * <type definitions for \uscheme>=
 */
typedef enum Letkeyword { LET, LETSTAR, LETREC } Letkeyword;
typedef struct Explist  *Explist;  /* list of Exp  */
/*
 * <type definitions for \uscheme>=
 */
typedef struct Valuelist *Valuelist;     /* list of Value */
typedef Value (Primitive)(Exp e, int tag, Valuelist vl);
/*
 * The definition of [[Primitive]] calls for
 * explanation, since it would be simpler to define a
 * primitive function as one that accepts a
 * [[Valuelist]] and returns a [[Value]]. We pass the
 * abstract syntax [[Exp e]] so that if the primitive
 * fails, it can issue a suitable error message. We pass
 * the integer [[tag]] so that we can write a single
 * C function that implements multiple primitives. For
 * example, the arithmetic primitives are implemented by
 * a single function, which makes it possible for them
 * to share the code that ensures both arguments are
 * numbers. Implementations of the primitives appear in
 * Section [->].
 */

/*
 * The Environment and the Store
 * 
 * [*] In the operational semantics, the store sigma is
 * intended to model the machine's memory. It should
 * come as no surprise, then, that we use C pointers (of
 * type [[Value *]]) as locations and the machine's
 * memory as the store. An environment [[Env]] maps
 * names to pointers; find(x, rho) returns rho(x) if x
 * in dom rho; otherwise it returns [[NULL]].
 * <type definitions for \uscheme>=
 */
typedef struct Env *Env;
/*
 * An input reader is just a line-reading function and
 * some extra state.
 * <shared structure definitions>=
 */
struct Reader {
    char *buf;               /* holds the last line read */
    int nbuf;                /* size of buf */
    int line;                /* current line number */
    const char *readername;  /* identifies this reader */

    FILE *fin;               /* filereader */
    const char *s;           /* stringreader */
};
/*
 * <shared structure definitions>=
 */
struct Par { Paralt alt; union { Name atom; Parlist list; } u; }; 
/*
 * <structure definitions for \uscheme>=
 */
struct Lambda { Namelist formals; Exp body; }; 
struct Value {
    Valuealt alt;
    union {
        int bool;
        int num;
        Name sym;
        struct { Value *car; Value *cdr; } pair;
        struct { Lambda lambda; Env env; } closure;
        struct { int tag; Primitive *function; } primitive;
    } u;
};

/*
 * <structure definitions for \uscheme>=
 */
struct Def {
    Defalt alt;
    union {
        struct { Name name; Exp exp; } val;
        Exp exp;
        struct { Name name; Lambda lambda; } define;
        Name use;
    } u;
};

struct Exp {
    Expalt alt;
    union {
        Value literal;
        Name var;
        struct { Name name; Exp exp; } set;
        struct { Exp cond; Exp true; Exp false; } ifx;
        struct { Exp cond; Exp body; } whilex;
        Explist begin;
        struct { Exp fn; Explist actuals; } apply;
        struct { Letkeyword let; Namelist nl; Explist el; Exp body; } letx;
        Lambda lambdax;
    } u;
};

/*
 * <structure definitions for \uscheme>=
 */
struct Explist {
	Exp hd;
	Explist tl;
};

struct Parlist {
	Par hd;
	Parlist tl;
};

struct Valuelist {
	Value hd;
	Valuelist tl;
};

struct Namelist {
	Name hd;
	Namelist tl;
};

/*
 * Pointer comparison is built into C, but we provide
 * two other operations on names.
 * <shared function prototypes>=
 */
Name strtoname(const char *s);
const char *nametostr(Name n);
/*
 * These functions satisfy the following algebraic laws:
 * 
 *  [[strcmp(s, nametostr(strtoname(s))) == 0]]
 *  [[strcmp(s, t) == 0]] if and only if [[strtoname
 *  (s) == strtoname(t)]]
 * 
 * Informally, the first law says if you build a name
 * from a string, [[nametostr]] returns a copy of your
 * original string. The second law says you can compare
 * names using pointer equality.
 */

/*
 * Function [[printname]] prints names.
 * <shared function prototypes>=
 */
Printer printname;
/*
 * <shared function prototypes>=
 */
char *readline(Reader r, char *prompt);
/*
 * Each of our interpreters leaves the prompt empty when
 * not reading interactively.
 */

/*
 * To create a reader, we need a string or a file.
 * A reader also gets a name, which we can use in error
 * messages. [*] [*]
 * <shared function prototypes>=
 */
Reader stringreader(const char *stringname, const char *s);
Reader filereader  (const char *filename,   FILE *fin);
/*
 * <shared function prototypes>=
 */
Def readdef(Defreader r);
/*
 * To create a definition reader, we need a source of
 * characters.
 */

/*
 * <shared function prototypes>=
 */
Defreader defreader(Reader r, int doprompt);
/*
 * The [[doprompt]] flag controls whether the resulting
 * [[Defreader]] prompts when reading input.
 */

/*
 * Printing
 * 
 * [*] The standard C function [[printf]] and its
 * siblings [[fprintf]] and [[vfprintf]] convert
 * internal C values to sequences of characters in an
 * output file. Unfortunately, they convert only
 * numbers, characters, and strings. It would be a lot
 * more convenient if [[printf]] also converted [[Name]]
 * s, [[Exp]]s, and so on. We can't change [[printf]],
 * so instead we define new functions. Functions
 * [[print]] and [[fprint]] are a bit like [[printf]]
 * and [[fprintf]].
 * <shared function prototypes>=
 */
void print (const char *fmt, ...);  /* print to standard output */
void fprint(FILE *output, const char *fmt, ...);  /* print to given file */
/*
 * The advantage of our versions is that they are
 * extensible; if we want to print new kinds of values,
 * like Impcore expressions, we can add new printing
 * functions.
 */

/*
 * To tell [[print]] and [[eprint]] about a new
 * extension, we announce the extension by calling
 * [[installprinter]] with the extension and with a
 * character that is used for the extension's
 * ``conversion specification.''
 * <shared function prototypes>=
 */
void installprinter(unsigned char c, Printer *fmt);
/*
 * The printer interface provides printers to format
 * percent signs, strings, and decimal integers.
 * <shared function prototypes>=
 */
Printer printpercent, printstring, printdecimal;
/*
 * If you are a sophisticated C programmer, you may want
 * to use our analog of [[vfprintf]]:
 * <shared function prototypes>=
 */
void vprint(FILE *output, const char *fmt, va_list_box *box);
/*
 * Error handling
 * 
 * Any module can signal an error by calling [[error]].
 * When called, [[error]] acts just like [[eprint]]
 * except that it does not return after printing;
 * instead it [[longjmp]]s to [[errorjmp]]. It is an
 * unchecked run-time error to call [[error]] except
 * while a suitable [[setjmp]] is active on the C call
 * stack. [*]
 * <shared function prototypes>=
 */
void error(const char *fmt, ...);
extern jmp_buf errorjmp;        /* longjmp here on error */
/*
 * Function [[checkargc]] is used to check the number of
 * arguments to both user-defined and primitive
 * functions. The first argument is an abstract-syntax
 * tree representing the application being checked; if
 * [[expected]] != [[actual]], [[checkargc]] calls
 * [[error]], passing a message that contains [[e]].
 * <shared function prototypes>=
 */
void checkargc(Exp e, int expected, int actual);
/*
 * The [[duplicatename]] function finds a duplicate name
 * on a [[Namelist]] if such a name exists. It is used
 * to check that formal parameters to user-defined
 * functions all have different names. If the name list
 * [[names]] contains a duplicate occurrence of any
 * name, the function returns such a name; otherwise it
 * returns [[NULL]].
 * <shared function prototypes>=
 */
Name duplicatename(Namelist names);
/*
 * <shared function prototypes>=
 */
Printer printpar;
/*
 * The [[readparlist]] function reads and returns a list
 * of parenthesized expressions from the given
 * [[Reader]], stopping when an end-of-expression and
 * end-of-line coincide. The [[doquote]] flag specifies
 * that an expression like [['(1 2 3)]] should be turned
 * into [[(quote (1 2 3))]]; it is used to implement
 * micro-Scheme. The [[doprompt]] flag specifies that
 * prompts should be printed when reading input lines.
 * <shared function prototypes>=
 */
Parlist readparlist(Reader r, int doquote, int doprompt);
/*
 * Stack-overflow detection
 * 
 * The first call to [[checkoverflow]] sets a
 * ``low-water mark'' in the stack. Each later call
 * checks the current stack pointer against that
 * low-water mark. If the distance exceeds [[limit]],
 * [[checkoverflow]] calls [[error]]. Otherwise it
 * returns the distance.
 * <shared function prototypes>=
 */
extern int checkoverflow(int limit);
/*
 * <shared function prototypes>=
 */
Par mkAtom(Name atom);
Par mkList(Parlist list);
struct Par mkAtomStruct(Name atom);
struct Par mkListStruct(Parlist list);
/*
 * <function prototypes for \uscheme>=
 */
Lambda mkLambda(Namelist formals, Exp body);
Value mkNil(void);
Value mkBool(int bool);
Value mkNum(int num);
Value mkSym(Name sym);
Value mkPair(Value *car, Value *cdr);
Value mkClosure(Lambda lambda, Env env);
Value mkPrimitive(int tag, Primitive *function);
/*
 * <function prototypes for \uscheme>=
 */
Def mkVal(Name name, Exp exp);
Def mkExp(Exp exp);
Def mkDefine(Name name, Lambda lambda);
Def mkUse(Name use);
struct Def mkValStruct(Name name, Exp exp);
struct Def mkExpStruct(Exp exp);
struct Def mkDefineStruct(Name name, Lambda lambda);
struct Def mkUseStruct(Name use);
Exp mkLiteral(Value literal);
Exp mkVar(Name var);
Exp mkSet(Name name, Exp exp);
Exp mkIfx(Exp cond, Exp true, Exp false);
Exp mkWhilex(Exp cond, Exp body);
Exp mkBegin(Explist begin);
Exp mkApply(Exp fn, Explist actuals);
Exp mkLetx(Letkeyword let, Namelist nl, Explist el, Exp body);
Exp mkLambdax(Lambda lambdax);
struct Exp mkLiteralStruct(Value literal);
struct Exp mkVarStruct(Name var);
struct Exp mkSetStruct(Name name, Exp exp);
struct Exp mkIfxStruct(Exp cond, Exp true, Exp false);
struct Exp mkWhilexStruct(Exp cond, Exp body);
struct Exp mkBeginStruct(Explist begin);
struct Exp mkApplyStruct(Exp fn, Explist actuals);
struct Exp mkLetxStruct(Letkeyword let, Namelist nl, Explist el, Exp body);
struct Exp mkLambdaxStruct(Lambda lambdax);
/*
 * <function prototypes for \uscheme>=
 */
int     lengthEL (Explist l);
Exp     nthEL    (Explist l, unsigned n);
Explist mkEL     (Exp hd, Explist tl);
Printer printexplist;
/*
 * <function prototypes for \uscheme>=
 */
int     lengthPL (Parlist l);
Par     nthPL    (Parlist l, unsigned n);
Parlist mkPL     (Par hd, Parlist tl);
Printer printparlist;
/*
 * <function prototypes for \uscheme>=
 */
int       lengthVL (Valuelist l);
Value     nthVL    (Valuelist l, unsigned n);
Valuelist mkVL     (Value hd, Valuelist tl);
Printer   printvaluelist;
/*
 * <function prototypes for \uscheme>=
 */
int      lengthNL (Namelist l);
Name     nthNL    (Namelist l, unsigned n);
Namelist mkNL     (Name hd, Namelist tl);
Printer  printnamelist;
/*
 * Scheme, S-expressions, and first-class functions
 * 
 * [*]
 * 
 */

/*
 * <function prototypes for \uscheme>=
 */
Value *find(Name name, Env env);
/*
 * The function [[bindalloc]] binds a name to a freshly
 * allocated location, and it puts a value in that
 * location. Formally, when called with store sigma,
 * bindalloc(x, v, rho) chooses an l\notindom sigma,
 * updates the store to be sigma{l|->v}, and returns the
 * extended environment rho{x |->l}.
 * <function prototypes for \uscheme>=
 */
Env bindalloc    (Name name,   Value v,      Env env);
Env bindalloclist(Namelist nl, Valuelist vl, Env env);
/*
 * Calling bindalloclist(<\ldotsnx>, <\ldotsnv>, rho)
 * does the same job for a list of values, returning rho
 * {x_1 |->l_1, ..., x_n |->l_n}, where \ldotsnl are
 * fresh locations, which [[bindalloclist]] initializes
 * to values \ldotsnv.
 */

/*
 * Allocation
 * 
 * The fresh locations created by [[bindalloc]] and
 * [[bindalloclist]] come from [[allocate]]. Calling
 * [[allocate(v)]] finds a location l\notindom sigma,
 * stores [[v]] in l (thereby updating sigma), and
 * returns l.
 * <function prototypes for \uscheme>=
 */
Value *allocate(Value v);
/*
 * Before the first call to [[allocate]], a client must
 * call [[initallocate]]. For reasons that are disclosed
 * in Chapter [->], [[initallocate]] requires [[envp]],
 * a pointer to the global environment, and it sets
 * [[*envp = NULL]].
 * <function prototypes for \uscheme>=
 */
void initallocate(Env *envp);
/*
 * Finally, if an error occurs during program execution,
 * a client must call [[resetallocate]], also passing a
 * pointer to the global environment.
 * <function prototypes for \uscheme>=
 */
void resetallocate(Env *envp);
/*
 * Chapter [->] describes allocation in detail.
 */

/*
 * Values
 * 
 * [*] The representation of values appears in chunk 
 * [->] in Section [->]. The value interface also
 * exports predefined values [[truev]] and [[falsev]],
 * which represent [[#t]] and [[#f]].
 * <function prototypes for \uscheme>=
 */
Value truev, falsev;
/*
 * Before executing any code that refers to [[truev]] or
 * [[falsev]], clients must call [[initvalue]].
 */

/*
 * <function prototypes for \uscheme>=
 */
void initvalue(void);
/*
 * Function [[istrue]] takes a value and returns [[1]]
 * if the value should be regarded as true (i.e., is not
 * [[#f]]) and [[0]] otherwise.
 * <function prototypes for \uscheme>=
 */
int istrue(Value v);
/*
 * Function [[unspecified]] returns an unspecified
 * value.
 * <function prototypes for \uscheme>=
 */
Value unspecified(void);
/*
 * For example, \monoboxeval(e, rho), when evaluated
 * with store sigma, finds a v and a sigma' such that \
 * evale ==>\evalr[']v, updates the store to be sigma',
 * and returns v.
 * <function prototypes for \uscheme>=
 */
Value eval   (Exp e, Env rho);
Env   evaldef(Def d, Env rho, int echo);
/*
 * Similarly, \monoboxevaldef(e, rho, echo), when
 * evaluated with store sigma, finds a rho' and a sigma'
 * such that \evaldefe -->\evaldefr', updates the store
 * to be sigma', and returns rho'. If [[echo]] is
 * nonzero, [[evaldef]] also prints the name or value of
 * whatever expression is evaluated or added to rho.
 */

/*
 * In our implementation of micro-Scheme,
 * [[readevalprint]] has side effects on an environment
 * pointer that is passed by reference. This technique
 * ensures that in an interactive session, errors don't
 * destroy the results of definitions and [[val]]
 * bindings that precede the error. If [[readevalprint]]
 * simply returned a new environment, then when an error
 * occurred, any partially created environment would be
 * lost.
 * <function prototypes for \uscheme>=
 */
void readevalprint(Defreader r, Env *envp, int echo);
/*
 * Primitives
 * 
 * Compared to Impcore, micro-Scheme has many
 * primitives. The function [[primenv]] returns an
 * environment binding all the primitive operations.
 * <function prototypes for \uscheme>=
 */
Env primenv(void);
/*
 * Here are some of the printing functions used.
 * <function prototypes for \uscheme>=
 */
void printenv    (FILE *output, va_list_box*);
void printvalue  (FILE *output, va_list_box*);
void printclosure(FILE *output, va_list_box*);
void printexp    (FILE *output, va_list_box*);
void printdef    (FILE *output, va_list_box*);
void printlambda (FILE *output, va_list_box*);
