#include <stdlib.h>

void foo_8_6(char *p) {
    p=(char*)malloc(sizeof(char));
}
void bar_8_6 () {
    foo_8_6((char *)malloc(sizeof(char)));
}

