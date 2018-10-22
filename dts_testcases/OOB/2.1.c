#include <stdlib.h>
struct A_2_1 {
	char *a;
	char b[5];
};

// Array
int foo_2_1() {
	struct A_2_1 a;
	a.b[5] = 'a';
	return 0;
}
// Memory
int bar_2_1() {
	struct A_2_1 a;
	a.a = 0;
	a.a = (char *)malloc(sizeof(char) * 5);
	a.a[5] = 'a';
	free(a.a);
	return 0;
}
