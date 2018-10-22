#include <stdlib.h>

char *p_8_2;
void foo_8_2 (char *p) {
    p_8_2=(char*)malloc(sizeof(char));
}
void bar_8_2() {
    foo_8_2 (p_8_2);
    p_8_2=(char*)malloc(sizeof(char));
}
