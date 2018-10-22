#include <stdlib.h>
// Array
char p[5][5];
void foo_6_5() {
	p[0][5] = 'a';
}
int bar_6_5() {
	foo_6_5();
	return 0;
}

// Memory
char *b[5];
void fooa_6_5() {
	b[0][5] = 'a';
}
int bara_6_5() {
	b[0] = (char *)malloc(sizeof(char) * 5);
	fooa_6_5();
	free(b[0]);
	return 0;
}
