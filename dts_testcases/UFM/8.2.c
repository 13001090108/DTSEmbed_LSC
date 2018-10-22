#include <stdlib.h>
char *p;
void foo_8_2(char *p) {
     *p;
}
void bar_8_2() {
	p = (char *)malloc(sizeof(char));
	free(p);
	foo_8_2(p);
}
