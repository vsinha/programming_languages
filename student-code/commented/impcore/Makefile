#
# Makefile for impcore
#

SOURCES  = ast.c definition-code.c env.c error.c eval.c\
           exp-code.c fun-code.c fun.c impcore.c lex.c\
           list-code.c name.c overflow.c par-code.c parse.c\
           print.c read.c value.c
HEADERS  = all.h
OBJECTS  = $(SOURCES:.c=.o)
RESULT   = impcore

CC = gcc -ansi -pedantic -Wall -Werror -Wextra -Wno-overlength-strings
CFLAGS = -g 
LDFLAGS = -g
CPPFLAGS = -I.
RM = rm -f 

.SUFFIXES:
.SUFFIXES: .c .o

$(RESULT): $(OBJECTS)
	$(CC) -o $@ $(LDFLAGS) $(OBJECTS)

.c.o:
	$(CC) $(CFLAGS) $(CPPFLAGS) -c $<

clean:
	$(RM) $(RESULT) *.o *.core core *~

ast.o: ast.c $(HEADERS)
env.o: env.c $(HEADERS)
eval.o: eval.c $(HEADERS)
error.o: error.c $(HEADERS)
fun.o: fun.c $(HEADERS)
impcore.o: impcore.c $(HEADERS)
lex.o: lex.c $(HEADERS)
name.o: name.c $(HEADERS)
overflow.o: overflow.c $(HEADERS)
parse.o: parse.c $(HEADERS)
print.o: print.c $(HEADERS)
read.o: read.c $(HEADERS)
value.o: value.c $(HEADERS)
exp-code.o: exp-code.c $(HEADERS)
definition-code.o: definition-code.c $(HEADERS)
fun-code.o: fun-code.c $(HEADERS)
list-code.o: list-code.c $(HEADERS)
par-code.o: par-code.c $(HEADERS)
