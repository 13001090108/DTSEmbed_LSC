#include <stdlib.h>
struct A_2_3 {
       char *p;
};
int foo_2_3(int i) {
    struct A_2_3 a;
    a.p=(char*)malloc(sizeof(char));
    if (i || a.p)
       return 0;
    free(a.p);
    return 0;
}










