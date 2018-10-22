#include <stdlib.h>
struct A_2_5 {
       char *p;
};
int foo_2_5() {
    struct A_2_5 a;
    a.p= (char*)malloc(sizeof(char));
    if (!a.p) ;
    return 0;
}












