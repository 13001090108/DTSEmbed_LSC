#include <stdlib.h>
struct A_8_3 {
	char p[5];
	char *b;
};
struct A_8_3 a;

// Array
void foo_8_3(char p) {
}
void bar_8_3() {
	foo_8_3(a.p[5]);
}

// Memory
void fooa_8_3(char p) {
}
void bara_8_3() {
	a.b = (char *)malloc(sizeof(char) * 5);
	fooa_8_3(a.b[5]);
}
