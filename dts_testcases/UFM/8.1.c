#include <stdlib.h>
void foo_8_1(char *p) {
     *p;
}
void bar_8_1(char *p) {
	p = (char *)malloc(sizeof(char));
	free(p);
	foo_8_1(p);
}
