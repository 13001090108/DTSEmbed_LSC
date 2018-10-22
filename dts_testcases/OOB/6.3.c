#include <stdlib.h>
struct A_6_3 {
	char p[5];
	char *b;
};
struct A_6_3 a;

// Array
void foo_6_3() {
	a.p[5] = 'a';
}
int bar_6_3() {
	foo_6_3();
	return 0;
}

// Memory
void fooa_6_3() {
	a.b[5] = 'a';
}
int bara_6_3() {
	a.b = (char *)malloc(sizeof(char) * 5);
	fooa_6_3();
	free(a.b);
	return 0;
}
