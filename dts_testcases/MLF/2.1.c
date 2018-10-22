#include <stdlib.h>
struct A_2_1 {
       char *p;
};
int foo_2_1() {
    struct A_2_1 a;
    a.p=(char*)malloc(sizeof(char));
    return 0;
}









