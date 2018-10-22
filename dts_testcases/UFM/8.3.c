#include <stdlib.h>
struct A_8_3 {
	char *p;
};
struct A_8_3 a;
void foo_8_3(char * p) {
     *p;
}
void bar_8_3() {
	a.p = (char *)malloc(sizeof(char));
	free(a.p);
	foo_8_3(a.p);
}
