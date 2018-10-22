#include <stdlib.h>
 #include <stdio.h>
 #include <string.h>
 void foo(FILE* f, char* pc, int i, char c) {
	 fprintf(f, "%c %s %k", c, pc);      // unknown specifier 'k'
	 fprintf(f, "%o", i);
   }
