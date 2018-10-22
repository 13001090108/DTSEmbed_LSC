#include <stdlib.h>

// Array
char p[5][5];
void foo_8_5(char p) {
}
void bar_8_5() {
	foo_8_5(p[0][5]);
}

// Memory
char *b[5];
void fooa_8_5(char p) {
}
void bara_8_5() {
	b[0] = (char *)malloc(sizeof(char) * 5);
	fooa_8_5(b[0][5]);
}

