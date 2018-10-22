#include <stdlib.h>
// Array
char p[5][5];
void foo_7_5() {
	p[0][5] = 'a';
}
void baz_7_5() {
	foo_7_5();
}
int bar_7_5() {
	baz_7_5();
	return 0;
}

// Memory
char *b[5];
void fooa_7_5() {
	b[0][5] = 'a';
}
void baza_7_5() {
	fooa_7_5();
}
int bara_7_5() {
	b[0] = (char *)malloc(sizeof(char) * 5);
	baza_7_5();
	free(b[0]);
	return 0;
}
