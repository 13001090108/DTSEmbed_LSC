#include <stdlib.h>

// Array
void foo_8_1(char p) {
}
void bar_8_1(char p[5]) {
	foo_8_1(p[5]);
}

// Memory
void fooa_8_1(char p) {
}
void bara_8_1(char *p) {
	p = (char *)malloc(sizeof(char) * 5);
	fooa_8_1(p[5]);
}

