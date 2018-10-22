#include <stdlib.h>
struct A_2_12 {
	char *p;
	char b[5];
};
struct A_2_12 a;
// Array
int foo_2_12(int i) {
	if (a.b[5] != 'a' || i) ;
	return 0;
}

// Memory
int bar_2_12(int i) {
	a.p = (int *)malloc(sizeof(int) * 5);
	if (i || a.p[5] != 'a') ;
	free(a.p);
	return 0;
}
