#include <stdlib.h>
char *foo_5_1() {
    char *p= (char*)malloc(sizeof(char));
    return p;
}
int bar_5_1() {
    char*q=foo_5_1();
    return 0;
}

