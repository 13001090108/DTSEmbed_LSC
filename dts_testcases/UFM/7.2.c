#include <stdlib.h>
char *p;
void foo_7_2() {
	*p = 'a';
}
void bar_7_2() {
	foo_7_2();
}
int baz_7_2() {
	p = (char *)malloc(sizeof(char));
	free(p);
	bar_7_2();
	//foo_7_2();
	return 0;
}
