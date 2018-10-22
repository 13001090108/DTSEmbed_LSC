#include <stdlib.h>
struct A_2_8 {
	int *p;
	char b[5];
};
struct A_2_8 a;
// Array
int foo_2_8(int i) {
	a.b[5] = 'a';
	if (!a.b[5] || i) ;
	return 0;
}

// Memory
int bar_2_8(int i) {
	a.p = (int *)malloc(sizeof(int) * 5);
	a.p[5] = 'a';
	if (!a.p || i) ;
	free(a.p);
	return 0;
}
