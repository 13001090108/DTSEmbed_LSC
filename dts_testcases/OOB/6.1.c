#include <stdlib.h>
// Array
void foo_6_1(char p[5]) {
	p[5] = 'a';
}
int bar_6_1() {
	char p[5] = {0};
	foo_6_1(p);
	return 0;
}

// Memory
void fooa_6_1(char *p) {
	p[5] = 'a';
}
int bara_6_1() {
	char *p = (char *)malloc(sizeof(char) * 5);
	fooa_6_1(p);
	free(p);
	return 0;
}
