#include <stdlib.h>
struct A_2_9 {
       char *p;
};

void setNull_2_9(char * p) {
     p= (char*)malloc(sizeof(char));
}
int foo_2_9() {
    struct A_2_9 a;
    setNull_2_9(a.p);
    return 0;
}












