#include <stdlib.h>
struct A_2_7 {
	int *p;
	char b[5];
};
struct A_2_7 a;
// Array
int foo_2_7() {
	a.b[5] = 'a';
	if (!a.b[5]) ;
	return 0;
}

// Memory
int bar_2_7() {
	a.p = (int *)malloc(sizeof(int) * 5);
	a.p[5] = 'a';
	if (!a.p) ;
	free(a.p);
	return 0;
}
