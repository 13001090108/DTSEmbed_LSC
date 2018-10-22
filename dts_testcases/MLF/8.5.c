#include <stdlib.h>

char *a_8_5[10];
void foo_8_5 (char *p) {
    p=(char*)malloc(sizeof(char));
}
void bar_8_5 () {
     foo_8_5 (a_8_5 [0]);
     a_8_5 [0]=(char*)malloc(sizeof(char));
}
