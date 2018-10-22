#include <stdlib.h>

struct A_8_3 {
    char *p;
};
struct A_8_3 a_8_3;
void foo_8_3 (char *p) {
    p=(char*)malloc(sizeof(char));
}
void bar_8_3 () {
     foo_8_3 (a_8_3.p);
     a_8_3.p=(char*)malloc(sizeof(char));
}
