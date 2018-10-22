#include <stdlib.h>
struct A_2_11 {
	char *p;
	char b[5];
};
struct A_2_11 a;
// Array
int foo_2_11() {
	if (a.b[5] != 'a') ;
	return 0;
}

// Memory
int bar_2_11() {
	a.p = (int *)malloc(sizeof(int) * 5);
	if (a.p[5] != 'a') ;
	free(a.p);
	return 0;
}
