#include <stdlib.h>

void foo_6_1(char *p) {
    p = (char*)malloc(sizeof(char));
}
int bar_6_1(int argc, char **argv) {
    char *p;
    foo_6_1(p);
    return 0;
}





