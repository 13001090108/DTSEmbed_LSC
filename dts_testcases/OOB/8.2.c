#include <stdlib.h>

// Array
char p[5];
void foo_8_2(char p) {
}
void bar_8_2() {
	foo_8_2(p[5]);
}

// Memory
char *b;
void fooa_8_2(char p) {
}
void bara_8_2() {
	b = (char *)malloc(sizeof(char) * 5);
	fooa_8_2(b[5]);
}

