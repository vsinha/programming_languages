/*
 * Arithmetic primitives
 * 
 * These are the arithmetic primitives. [*]
 * <prim.h>=
 */
xx("+", PLUS,  arith)
xx("-", MINUS, arith)
xx("*", TIMES, arith)
xx("/", DIV,   arith)
xx("<", LT,    arith)
xx(">", GT,    arith)
/*
 * Other binary primitives
 * 
 * micro-Scheme has two binary primitives that do not
 * require integer arguments. They are:
 * <prim.h>=
 */
xx("cons", CONS, binary)
xx("=",    EQ,   binary)
/*
 * Unary primitives
 * 
 * Finally, here are the unary primitives.
 * <prim.h>=
 */
xx("boolean?",   BOOLEANP,   unary)
xx("null?",      NULLP,      unary)
xx("number?",    NUMBERP,    unary)
xx("pair?",      PAIRP,      unary)
xx("procedure?", PROCEDUREP, unary)
xx("symbol?",    SYMBOLP,    unary)
xx("car",        CAR,        unary)
xx("cdr",        CDR,        unary)
xx("print",      PRINT,      unary)
xx("error",      ERROR,      unary)
