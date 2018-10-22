#include <stdlib.h>

void foo_8_7(char *p) {
    p=(char*)malloc(sizeof(char));
}
char *myalloc_8_7() {
    return (char *)malloc(sizeof(char));
}
void bar_8_7() {
    foo_8_7(myalloc_8_7());
}
