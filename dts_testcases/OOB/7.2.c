#include <stdlib.h>
// Array
char p[5];
void foo_7_2() {
	p[5] = 'a';
}
void baz_7_2() {
	foo_7_2();
}
int bar_7_2() {
	baz_7_2();
	return 0;
}

// Memory
char *b;
void fooa_7_2() {
	b[5] = 'a';
}
void baza_7_2() {
	fooa_7_2();
}
int bara_7_2() {
	b = (char *)malloc(sizeof(char) * 5);
	baza_7_2();
	free(b);
	return 0;
}

