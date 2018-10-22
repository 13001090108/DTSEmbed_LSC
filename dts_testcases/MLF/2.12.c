#include <stdlib.h>
struct A_2_12 {
       char *p;
};
int foo_2_12(int i) {
    struct A_2_12 a;
    if ((i == 1) && (a.p=(char*)malloc(sizeof(char))) ) {
       return 0;
        }
    return 0;
}












