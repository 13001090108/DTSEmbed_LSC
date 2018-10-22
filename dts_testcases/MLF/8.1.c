#include <stdlib.h>

void bar_8_1(char *p) {
     p = (char*)malloc(sizeof(char));
}
int main_8_1() {
	char ** argv;
    bar_8_1(argv);
    return 0;
}

