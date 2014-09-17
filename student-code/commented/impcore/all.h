/*
 * The header file is split into three parts: type
 * definitions, then structure definitions, then
 * function prototypes. These splits make it easy for
 * functions or structures declared in one interface to
 * use types defined in another; because declarations
 * and definitions of types always precede the function
 * prototypes that use those types, we need not worry
 * about getting things in the right order. So we can
 * reuse some of the code in this interpreter in later
 * interpreters, we also distinguish between shared and
 * unshared definitions; a definition is ``shared'' if
 * it is used in another interpreter later in the book.
 * <{\Tt all.h} for \impcore>=
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
 * We also define a type for lists of [[Exp]]s.
 * <type definitions for \impcore>=
 */
typedef struct Explist *Explist; /* list of Exp */
/*
 * An [[Explist]] is list of pointers of type [[Exp]].
 * We use this naming convention throughout our C code.
 * The definitions of our list types are in the lists
 * interface, in chunk [->].
 */

/*
 * Values
 * 
 * The value interface defines the type of value that
 * our expressions evaluate to. Impcore supports only
 * integers. A [[Valuelist]] is a list of [[Value]]s.
 * <type definitions for \impcore>=
 */
typedef int Value;
typedef struct Valuelist *Valuelist;     /* list of Value */
/*
 * Functions
 * 
 * In the Impcore interpreter, the type ``function'' is
 * another discriminated-union type. There are two
 * alternatives: user-defined functions and primitive
 * functions. Just like the operational semantics, which
 * represents a user-defined function as \user(<x_1,
 * ..., x_n>, e), the interpreter represents a
 * user-defined function as a pair containing formals
 * and body. The interpreter represents each primitive
 * by its name.
 * <type definitions for \impcore>=
 */
typedef struct Funlist *Funlist; /* list of Fun */
/*
 * Environments
 * 
 * In the operational semantics, the environments rho
 *  and xi hold values, and the environment phi holds
 * functions. To represent these two kinds of
 * environments, C offers these choices:
 * 
 *   * We can define one C type for environments that
 *  hold a [[Value]] and another for environments
 *  that hold a [[Fun]], and we can define two
 *  versions of each function. This choice guarantees
 *  type safety, but requires duplication of code.
 *   * We can define a single C type for environments
 *  that hold a [[void*]] pointer, define a single
 *  version of each function, and use type casting to
 *  convert a [[void*]] to a [[Value*]] or [[Fun*]]
 *  as needed. This choice duplicates no code, but it
 *  is unsafe; if we accidentally put a [[Value*]] in
 *  an environment intended to hold a [[Fun*]], it is
 *  an error that neither the C compiler nor the
 *  run-time system can detect.
 * 
 * In the interests of safety, we duplicate code.
 * Chapter [->] shows how in another implementation
 * language, ML, we can use polymorphism to achieve type
 * safety without duplicating code.
 * <type definitions for \impcore>=
 */
typedef struct Valenv *Valenv;
typedef struct Funenv *Funenv;
/*
 * <type definitions for \impcore>=
 */
typedef struct Exp *Exp;
typedef enum { LITERAL, VAR, SET, IFX, WHILEX, BEGIN, APPLY } Expalt;

/*
 * <type definitions for \impcore>=
 */
typedef struct Userfun Userfun; 
typedef struct Def *Def;
typedef enum { VAL, EXP, DEFINE, USE } Defalt; 
/*
 * <type definitions for \impcore>=
 */
typedef struct Fun Fun;
typedef enum { USERDEF, PRIMITIVE } Funalt; 
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
 * <structure definitions for \impcore>=
 */
struct Exp {
    Expalt alt;
    union {
        Value literal;
        Name var;
        struct { Name name; Exp exp; } set;
        struct { Exp cond; Exp true; Exp false; } ifx;
        struct { Exp cond; Exp exp; } whilex;
        Explist begin;
        struct { Name name; Explist actuals; } apply;
    } u;
};

/*
 * <structure definitions for \impcore>=
 */
struct Userfun { Namelist formals; Exp body; }; 
struct Def {
    Defalt alt;
    union {
        struct { Name name; Exp exp; } val;
        Exp exp;
        struct { Name name; Userfun userfun; } define;
        Name use;
    } u;
};

/*
 * <structure definitions for \impcore>=
 */
struct Fun { Funalt alt; union { Userfun userdef; Name primitive; } u; }; 
/*
 * <structure definitions for \impcore>=
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

struct Funlist {
	Fun hd;
	Funlist tl;
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
 * For debugging, it's convenient to be able to print
 * abstract-syntax trees, and we provide functions to do
 * so. These functions are set up to work with our
 * extensible replacement for [[printf]] (Section [->]);
 * the type [[Printer]] is defined in chunk [->].
 * <function prototypes for \impcore>=
 */
Printer printexp, printdef;
/*
 * <function prototypes for \impcore>=
 */
Printer printvalue;
/*
 * Finally, the module exports a print function.
 * <function prototypes for \impcore>=
 */
Printer printfun;
/*
 * A new environment may be created by passing a list of
 * names and a list of associated values or function
 * definitions. For example, mkValenv(<x_1, ..., x_n>,
 * <v_1, ..., v_n>) returns the environment {x_1 |->v_1,
 * ..., x_n |->v_n}. If the two lists are not the same
 * length, it is a checked runtime error.
 * <function prototypes for \impcore>=
 */
Valenv mkValenv(Namelist vars, Valuelist vals);
Funenv mkFunenv(Namelist vars, Funlist   defs);
/*
 * To retrieve a value or function definition, we use
 * [[fetchval]] or [[fetchfun]]. In the operational
 * semantics, we write the lookup fetchval(x, rho)
 * simply as rho(x).
 * <function prototypes for \impcore>=
 */
Value fetchval(Name name, Valenv env);
Fun   fetchfun(Name name, Funenv env);
/*
 * If the given name does not appear in the environment,
 * it is a checked runtime error. To avoid such errors,
 * we can call [[isvalbound]] or [[isfunbound]]; they
 * return [[1]] if the given name is in the environment,
 * and [[0]] otherwise. Formally, isvalbound(x, rho) is
 * written x in dom rho.
 */

/*
 * <function prototypes for \impcore>=
 */
int isvalbound(Name name, Valenv env);
int isfunbound(Name name, Funenv env);
/*
 * To add new bindings to an environment, use
 * [[bindval]] and [[bindfun]]. Unlike previous
 * operations on environments, [[bindval]] and
 * [[bindfun]] cannot be specified as pure functions.
 * Instead, [[bindval]] and [[bindfun]] mutate their
 * environments, replacing the old bindings with new
 * ones. Calling bindval(x, v, rho) is equivalent to
 * performing the assignment rho := rho{x |->v}. Because
 * rho is a mutable abstraction, the caller can see the
 * modifications to the environment.
 */

/*
 * <function prototypes for \impcore>=
 */
void bindval(Name name, Value val, Valenv env);
void bindfun(Name name, Fun   fun, Funenv env);
/*
 * These functions can be used to replace existing
 * bindings or to add new ones.
 */

/*
 * Evaluation
 * 
 * The evaluator's interface is not very interesting: it
 * is the implementation, which starts on page [->],
 * that is interesting. The function [[evaldef]]
 * corresponds to the --> relation in our operational
 * semantics, while [[eval]] corresponds to the ==>
 * relation. For example, eval(e, xi, phi, rho) finds a
 * v, xi', and rho' such that \evale ==>\eval[']v,
 * assigns rho := rho' and xi := xi', and returns v.
 * <function prototypes for \impcore>=
 */
void  evaldef(Def d, Valenv globals, Funenv functions, int echo);
Value eval   (Exp e, Valenv globals, Funenv functions, Valenv formals);
/*
 * If the [[echo]] parameter to [[evaldef]] is nonzero,
 * [[evaldef]] prints the values and names of top-level
 * expressions and functions. As with the formal rules
 * of the operational semantics, we can see from the
 * result types that evaluating a [[Def]] does not
 * produce a [[Value]], but evaluating an [[Exp]] does
 * produce a value. Both kind of evaluations can have
 * side effects on environments.
 */

/*
 * The function [[readevalprint]] consumes all of an
 * input source, evaluating each definition. As for
 * [[evaldef]], the [[echo]] parameter controls whether
 * [[readevalprint]] prints the values and names of
 * top-level expressions and functions.
 * <function prototypes for \impcore>=
 */
void readevalprint(Defreader r, Valenv globals, Funenv functions, int echo);
/*
 * <function prototypes for \impcore>=
 */
Exp mkLiteral(Value literal);
Exp mkVar(Name var);
Exp mkSet(Name name, Exp exp);
Exp mkIfx(Exp cond, Exp true, Exp false);
Exp mkWhilex(Exp cond, Exp exp);
Exp mkBegin(Explist begin);
Exp mkApply(Name name, Explist actuals);
struct Exp mkLiteralStruct(Value literal);
struct Exp mkVarStruct(Name var);
struct Exp mkSetStruct(Name name, Exp exp);
struct Exp mkIfxStruct(Exp cond, Exp true, Exp false);
struct Exp mkWhilexStruct(Exp cond, Exp exp);
struct Exp mkBeginStruct(Explist begin);
struct Exp mkApplyStruct(Name name, Explist actuals);
/*
 * <function prototypes for \impcore>=
 */
Userfun mkUserfun(Namelist formals, Exp body);
Def mkVal(Name name, Exp exp);
Def mkExp(Exp exp);
Def mkDefine(Name name, Userfun userfun);
Def mkUse(Name use);
struct Def mkValStruct(Name name, Exp exp);
struct Def mkExpStruct(Exp exp);
struct Def mkDefineStruct(Name name, Userfun userfun);
struct Def mkUseStruct(Name use);
/*
 * <function prototypes for \impcore>=
 */
Fun mkUserdef(Userfun userdef);
Fun mkPrimitive(Name primitive);
/*
 * <function prototypes for \impcore>=
 */
int     lengthEL (Explist l);
Exp     nthEL    (Explist l, unsigned n);
Explist mkEL     (Exp hd, Explist tl);
Printer printexplist;
/*
 * <function prototypes for \impcore>=
 */
int     lengthPL (Parlist l);
Par     nthPL    (Parlist l, unsigned n);
Parlist mkPL     (Par hd, Parlist tl);
Printer printparlist;
/*
 * <function prototypes for \impcore>=
 */
int       lengthVL (Valuelist l);
Value     nthVL    (Valuelist l, unsigned n);
Valuelist mkVL     (Value hd, Valuelist tl);
Printer   printvaluelist;
/*
 * <function prototypes for \impcore>=
 */
int     lengthFL (Funlist l);
Fun     nthFL    (Funlist l, unsigned n);
Funlist mkFL     (Fun hd, Funlist tl);
Printer printfunlist;
/*
 * <function prototypes for \impcore>=
 */
int      lengthNL (Namelist l);
Name     nthNL    (Namelist l, unsigned n);
Namelist mkNL     (Name hd, Namelist tl);
Printer  printnamelist;
