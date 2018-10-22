#include <stdlib.h>
// Array
char p[5];
void foo_6_2() {
	p[5] = 'a';
}
int bar_6_2() {
	foo_6_2();
	return 0;
}

// Memory
char *b;
void fooa_6_2() {
	b[5] = 'a';
}
int bara_6_2() {
	b = (char *)malloc(sizeof(char) * 5);
	fooa_6_2();
	free(b);
	return 0;
}
