/*
 * Implementations of the primitives
 * 
 * [*] We associate each primitive with a unique tag,
 * which identifies the primitive. We also associate the
 * primitive with a function, which implements the
 * primitive. The tags make it easy for one function to
 * implement more than one primitive, which makes it
 * easy for similar primitives to share code. We use the
 * following functions to implement primitives:
 * 
 *  [[arith]]  Arithmetic functions, which expect
 *             integers as arguments
 *  [[binary]] Non-arithmetic functions of two
 *             arguments
 *  [[unary]]  Functions of one argument
 * 
 * <prim.c>=
 */
#include "all.h"

static Primitive arith, binary, unary;
/*
 * To define the primitives and create these
 * associations, we resort to macro madness. Each
 * primitive appears in file prim.h as a macro [[xx(]]
 * name[[, ]]tag[[, ]]function[[)]]. We use the same
 * macros with two different definitions of [[xx]]: one
 * to create an enumeration with distinct tags, and one
 * to install the primitives in an empty environment.
 * There are other initialization techniques that don't
 * require macros, but this technique ensures there is a
 * single point of truth about the primitives (that
 * point of truth is the file prim.h), which helps us
 * ensure that the enumeration type is consistent with
 * the initialization code.
 * <prim.c>=
 */
enum {
  #define xx(NAME, TAG, FUNCTION) TAG,
  #include "prim.h"
  #undef xx
  UNUSED_TAG
};
/*
 * <prim.c>=
 */
Env primenv(void) {
    Env env = NULL;
    pushroot(mkEnvroot(&env));
    #define xx(NAME, TAG, FUNCTION) \
        env = bindalloc(strtoname(NAME), mkPrimitive(TAG, FUNCTION), env);
    #include "prim.h"
    #undef xx
    poproot(mkEnvroot(&env));
    return env;
}
/*
 * Each arithmetic primitive expects two integer
 * arguments, so we need to be able to project
 * micro-Scheme values into C integers. The projection
 * function [[projectint]] takes not only a value but
 * also an expression, so it can issue an informative
 * error message.
 * <prim.c>=
 */
static int projectint(Exp e, Value v) {
    if (v.alt != NUM)
        error("in %e, expected an integer, but got %v", e, v);
    return v.u.num;
}
/*
 * We need special support for division, because while
 * micro-Scheme requires that division round toward
 * minus infinity, C guarantees only that dividing
 * positive operands rounds toward zero.
 * <prim.c>=
 */
static int divide(int n, int m) {
    if (n >= 0)
        if (m >= 0)
            return n / m;
        else
            return -(( n - m - 1) / -m);
    else
        if (m >= 0)
            return -((-n + m - 1) /  m);
        else
            return -n / -m;
}
/*
 * Given the functions above, we can write [[arith]] as
 * a function that first converts its arguments to
 * integers, then does a [[switch]] to determine what to
 * do with those integers. The result is converted back
 * to a micro-Scheme value by either [[mkNum]] or
 * [[mkBool]], both of which are generated automatically
 * from the definition of [[Value]] in code chunk [->].
 * <prim.c>=
 */
static Value arith(Exp e, int tag, Valuelist args) {
    int n, m;

    checkargc(e, 2, lengthVL(args));
    n = projectint(e, nthVL(args, 0));
    m = projectint(e, nthVL(args, 1));

    switch (tag) {
    case PLUS:
        return mkNum(n + m);
    case MINUS:
        return mkNum(n - m);
    case TIMES:
        return mkNum(n * m);
    case DIV:
        if (m==0)
            error("division by zero");
        return mkNum(divide(n, m));
    case LT:
        return mkBool(n < m);
    case GT:
        return mkBool(n > m);
    default:
        assert(0);
        return falsev;
    }
}
/*
 * We implement them with the function [[binary]].
 * <prim.c>=
 */
static Value binary(Exp e, int tag, Valuelist args) {
    Value v, w;

    checkargc(e, 2, lengthVL(args));
    v = nthVL(args, 0);
    w = nthVL(args, 1);

    switch (tag) {
    case CONS:
        /*
         * <return cons cell containing [[v]] and [[w]]>=
         */
        {
            Value *l;
            Value rv;

            pushroot(mkStackvalueroot(&v));
            pushroot(mkStackvalueroot(&w));
            l = allocate(v);
            pushroot(mkHeaplocroot(&l));
            rv = mkPair(l, allocate(w));
            poproot(mkHeaplocroot(&l));
            poproot(mkStackvalueroot(&w));
            poproot(mkStackvalueroot(&v));
            return rv;
        }
    case EQ: 
        /*
         * The implementation of equality is not completely
         * trivial. Two values are [[=]] only if they are the
         * same number, the same boolean, the same symbol, or
         * both nil.
         * <return [[(= v w)]]>=
         */
        if (v.alt != w.alt)
            return falsev;

        switch (v.alt) {
        case NUM:
            return mkBool(v.u.num  == w.u.num);
        case BOOL:
            return mkBool(v.u.bool == w.u.bool);
        case SYM:
            return mkBool(v.u.sym  == w.u.sym);
        case NIL:
            return truev;
        default:
            return falsev;
        }
    }
    assert(0);
    return falsev; /* not reached */
}
/*
 * Here are the implementations.
 * <prim.c>=
 */
static Value unary(Exp e, int tag, Valuelist args) {
    Value v;

    checkargc(e, 1, lengthVL(args));
    v = nthVL(args, 0);
    switch (tag) {
    case NULLP:
        return mkBool(v.alt == NIL);
    case BOOLEANP:
        return mkBool(v.alt == BOOL);
    case NUMBERP:
        return mkBool(v.alt == NUM);
    case SYMBOLP:
        return mkBool(v.alt == SYM);
    case PAIRP:
        return mkBool(v.alt == PAIR);
    case PROCEDUREP:
        return mkBool(v.alt == CLOSURE || v.alt == PRIMITIVE);
    case CAR:
        if (v.alt != PAIR)
            error("car applied to non-pair %v in %e", v, e);
        return *v.u.pair.car;
    case CDR:
        if (v.alt != PAIR)
            error("cdr applied to non-pair %v in %e", v, e);
        return *v.u.pair.cdr;
    case PRINT:
        print("%v\n", v);
        return v;
    case ERROR:
        error("%v", v);
        return v;
    default:
        assert(0);
        return falsev; /* not reached */
    }
}
