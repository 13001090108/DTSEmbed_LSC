#include <stdlib.h>
#include <stdio.h>
#include<string.h>
void foo(FILE* f, char* pc, int i, char c) {
	fprintf(f, "%c %s", c);      // too few parameters
 fprintf(f, "%p", pc);
 }
