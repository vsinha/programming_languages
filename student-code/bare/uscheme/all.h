/* {\Tt all.h} for \uscheme 125c */
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <setjmp.h>
#include <ctype.h>
/* shared type definitions 28c */
typedef struct Name *Name;
typedef struct Namelist *Namelist;   /* list of Name */
/* shared type definitions 31a */
typedef struct Reader *Reader;
/* shared type definitions 31d */
typedef struct Defreader *Defreader;
/* shared type definitions 34a */
/* definition of [[va_list_box]] 35a */
typedef struct va_list_box {
  va_list ap;
} va_list_box;
typedef void Printer(FILE *output, va_list_box*);
/* shared type definitions 585d */
typedef struct Parlist *Parlist; /* list of Par */
/* shared type definitions (generated by a script) */
typedef struct Par *Par;
typedef enum { ATOM, LIST } Paralt; 
/* type definitions for \uscheme (generated by a script) */
typedef struct Lambda Lambda; 
typedef struct Value Value;
typedef enum { NIL, BOOL, NUM, SYM, PAIR, CLOSURE, PRIMITIVE } Valuealt;

/* type definitions for \uscheme (generated by a script) */
typedef struct Def *Def;
typedef enum { VAL, EXP, DEFINE, USE } Defalt; 
typedef struct Exp *Exp;
typedef enum {
    LITERAL, VAR, SET, IFX, WHILEX, BEGIN, APPLY, LETX, LAMBDAX
} Expalt;

/* type definitions for \uscheme 114b */
typedef enum Letkeyword { LET, LETSTAR, LETREC } Letkeyword;
typedef struct Explist  *Explist;  /* list of Exp  */
/* type definitions for \uscheme 114d */
typedef struct Valuelist *Valuelist;     /* list of Value */
typedef Value (Primitive)(Exp e, int tag, Valuelist vl);
/* type definitions for \uscheme 126a */
typedef struct Env *Env;
/* shared structure definitions 588c */
struct Reader {
    char *buf;               /* holds the last line read */
    int nbuf;                /* size of buf */
    int line;                /* current line number */
    const char *readername;  /* identifies this reader */

    FILE *fin;               /* filereader */
    const char *s;           /* stringreader */
};
/* shared structure definitions (generated by a script) */
struct Par { Paralt alt; union { Name atom; Parlist list; } u; }; 
/* structure definitions for \uscheme (generated by a script) */
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

/* structure definitions for \uscheme (generated by a script) */
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

/* structure definitions for \uscheme (generated by a script) */
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

/* shared function prototypes 28d */
Name strtoname(const char *s);
const char *nametostr(Name n);
/* shared function prototypes 28e */
Printer printname;
/* shared function prototypes 31b */
char *readline(Reader r, char *prompt);
/* shared function prototypes 31c */
Reader stringreader(const char *stringname, const char *s);
Reader filereader  (const char *filename,   FILE *fin);
/* shared function prototypes 31e */
Def readdef(Defreader r);
/* shared function prototypes 31f */
Defreader defreader(Reader r, int doprompt);
/* shared function prototypes 33f */
void print (const char *fmt, ...);  /* print to standard output */
void fprint(FILE *output, const char *fmt, ...);  /* print to given file */
/* shared function prototypes 34b */
void installprinter(unsigned char c, Printer *fmt);
/* shared function prototypes 34c */
Printer printpercent, printstring, printdecimal;
/* shared function prototypes 34d */
void vprint(FILE *output, const char *fmt, va_list_box *box);
/* shared function prototypes 35b */
void error(const char *fmt, ...);
extern jmp_buf errorjmp;        /* longjmp here on error */
/* shared function prototypes 35c */
void checkargc(Exp e, int expected, int actual);
/* shared function prototypes 35d */
Name duplicatename(Namelist names);
/* shared function prototypes 585e */
Printer printpar;
/* shared function prototypes 585f */
Parlist readparlist(Reader r, int doquote, int doprompt);
/* shared function prototypes 591c */
extern int checkoverflow(int limit);
/* shared function prototypes (generated by a script) */
Par mkAtom(Name atom);
Par mkList(Parlist list);
struct Par mkAtomStruct(Name atom);
struct Par mkListStruct(Parlist list);
/* function prototypes for \uscheme (generated by a script) */
Lambda mkLambda(Namelist formals, Exp body);
Value mkNil(void);
Value mkBool(int bool);
Value mkNum(int num);
Value mkSym(Name sym);
Value mkPair(Value *car, Value *cdr);
Value mkClosure(Lambda lambda, Env env);
Value mkPrimitive(int tag, Primitive *function);
/* function prototypes for \uscheme (generated by a script) */
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
/* function prototypes for \uscheme (generated by a script) */
int     lengthEL (Explist l);
Exp     nthEL    (Explist l, unsigned n);
Explist mkEL     (Exp hd, Explist tl);
Printer printexplist;
/* function prototypes for \uscheme (generated by a script) */
int     lengthPL (Parlist l);
Par     nthPL    (Parlist l, unsigned n);
Parlist mkPL     (Par hd, Parlist tl);
Printer printparlist;
/* function prototypes for \uscheme (generated by a script) */
int       lengthVL (Valuelist l);
Value     nthVL    (Valuelist l, unsigned n);
Valuelist mkVL     (Value hd, Valuelist tl);
Printer   printvaluelist;
/* function prototypes for \uscheme (generated by a script) */
int      lengthNL (Namelist l);
Name     nthNL    (Namelist l, unsigned n);
Namelist mkNL     (Name hd, Namelist tl);
Printer  printnamelist;
/* function prototypes for \uscheme 126b */
Value *find(Name name, Env env);
/* function prototypes for \uscheme 126c */
Env bindalloc    (Name name,   Value v,      Env env);
Env bindalloclist(Namelist nl, Valuelist vl, Env env);
/* function prototypes for \uscheme 126d */
Value *allocate(Value v);
/* function prototypes for \uscheme 126e */
void initallocate(Env *envp);
/* function prototypes for \uscheme 127a */
void resetallocate(Env *envp);
/* function prototypes for \uscheme 127b */
Value truev, falsev;
/* function prototypes for \uscheme 127c */
void initvalue(void);
/* function prototypes for \uscheme 127d */
int istrue(Value v);
/* function prototypes for \uscheme 127e */
Value unspecified(void);
/* function prototypes for \uscheme 127f */
Value eval   (Exp e, Env rho);
Env   evaldef(Def d, Env rho, int echo);
/* function prototypes for \uscheme 127g */
void readevalprint(Defreader r, Env *envp, int echo);
/* function prototypes for \uscheme 128a */
Env primenv(void);
/* function prototypes for \uscheme 128b */
void printenv    (FILE *output, va_list_box*);
void printvalue  (FILE *output, va_list_box*);
void printclosure(FILE *output, va_list_box*);
void printexp    (FILE *output, va_list_box*);
void printdef    (FILE *output, va_list_box*);
void printlambda (FILE *output, va_list_box*);
