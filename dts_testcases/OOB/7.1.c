#include <stdlib.h>
// Array
void foo_7_1(char p[5]) {
	p[5] = 'a';
}
void baz_7_1(char p[5]) {
	foo_7_1(p);
}
int bar_7_1() {
	char p[5] = {0};
	baz_7_1(p);
	return 0;
}

// Memory
void fooa_7_1(char *p) {
	p[5] = 'a';
}
void baza_7_1(char *p) {
	fooa_7_1(p);
}
int bara_7_1() {
	char *p = (char *)malloc(sizeof(char) * 5);
	baza_7_1(p);
	free(p);
	return 0;
}

