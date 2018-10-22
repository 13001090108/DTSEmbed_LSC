#include <stdlib.h>
struct A_2_5 {
	int *p;
	char b[5];
};
struct A_2_5 a;
// Array
int foo_2_5() {
	if (!a.b[5]) ;
	a.b[5] = 'a';
	return 0;
}

// Memory
int bar_2_5() {
	a.p = (int *)malloc(sizeof(int) * 5);
	if (!a.p) ;
	a.p[5] = 'a';
	free(a.p);
	return 0;
}
