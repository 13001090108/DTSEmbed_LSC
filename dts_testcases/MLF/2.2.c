#include <stdlib.h>
struct A_2_2 {
       char *p;
};
int foo_2_2() {
    struct A_2_2 a;
    a.p=(char*)malloc(sizeof(char));
    if (a.p)
       return 0;
    free(a.p);
    return 0;
}









