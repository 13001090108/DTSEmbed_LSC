#include <stdlib.h>
struct A_2_6 {
	int *p;
	char b[5];
};
struct A_2_6 a;
// Array
int foo_2_6(int i) {
	if (!a.b[5] || i) ;
	a.b[5] = 'a';
	return 0;
}

// Memory
int bar_2_6(int i) {
	a.p = (int *)malloc(sizeof(int) * 5);
	if (!a.p || i) ;
	a.p[5] = 'a';
	free(a.p);
	return 0;
}
