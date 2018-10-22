#include <stdlib.h>
struct A_6_3 {
	char *p;
};
struct A_6_3 a;
void foo_6_3() {
	*(a.p) = 'a';
}
int ff_6_3() {
	a.p = (char *)malloc(sizeof(char));
	free(a.p);
	foo_6_3();
	return 0;
}
