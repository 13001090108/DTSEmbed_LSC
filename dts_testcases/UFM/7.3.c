#include <stdlib.h>
struct A_7_3 {
	char *p;
};
struct A_7_3 a;
void foo_7_3() {
	*(a.p) = 'a';
}
void bar_7_3() {
	foo_7_3();
}
int baz_7_3() {
	a.p = (char *)malloc(sizeof(char));
	free(a.p);
	bar_7_3();
	//foo_7_3();
	return 0;
}
