#include <stdlib.h>
void foo_8_6(char p) {
}
void bar_8_6() {
	foo_8_6(*(char *)malloc(sizeof(char)));
}
