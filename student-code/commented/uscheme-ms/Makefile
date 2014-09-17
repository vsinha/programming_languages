#
# Makefile for uscheme-ms
#

SOURCES  = ast-code.c ast.c env.c error.c eval.c lex.c\
           list-code.c loc.c ms.c name.c overflow.c\
           par-code.c parse.c prim.c print.c read.c\
           root-code.c root.c scheme.c value-code.c value.c
HEADERS  = all.h prim.h
OBJECTS  = $(SOURCES:.c=.o)
RESULT   = uscheme-ms

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
error.o: error.c $(HEADERS)
eval.o: eval.c $(HEADERS)
lex.o: lex.c $(HEADERS)
loc.o: loc.c $(HEADERS)
ms.o: ms.c $(HEADERS)
name.o: name.c $(HEADERS)
overflow.o: overflow.c $(HEADERS)
parse.o: parse.c $(HEADERS)
prim.o: prim.c $(HEADERS)
print.o: print.c $(HEADERS)
read.o: read.c $(HEADERS)
root.o: root.c $(HEADERS)
scheme.o: scheme.c $(HEADERS)
value.o: value.c $(HEADERS)
value-code.o: value-code.c $(HEADERS)
ast-code.o: ast-code.c $(HEADERS)
par-code.o: par-code.c $(HEADERS)
list-code.o: list-code.c $(HEADERS)
root-code.o: root-code.c $(HEADERS)
