#include <stdlib.h>
struct A_7_3 {
	char p[5];
	char *b;
};
struct A_7_3 a;
// Array
void foo_7_3() {
	a.p[5] = 'a';
}
void baz_7_3() {
	foo_7_3();
}
int bar_7_3() {
	baz_7_3();
	return 0;
}

// Memory
void fooa_7_3() {
	a.b[5] = 'a';
}
void baza_7_3() {
	fooa_7_3();
}
int bara_7_3() {
	a.b = (char *)malloc(sizeof(char) * 5);
	baza_7_3();
	free(a.b);
	return 0;
}

