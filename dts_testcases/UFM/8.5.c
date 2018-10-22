#include <stdlib.h>
char *p[10];
void foo_8_5() {
     *p[0];
}
void bar_8_5() {
	p[0] = (char *)malloc(sizeof(char));
	free(p[0]);
	foo_8_5();
}
