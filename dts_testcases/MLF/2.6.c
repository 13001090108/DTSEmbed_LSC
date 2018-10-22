#include <stdlib.h>
struct A_2_6 {
       char *p;
};
int foo_2_6(int i) {
    struct A_2_6 a;
    a.p= (char*)malloc(sizeof(char));
    if (i || !a.p) ;
    return 0;
}













