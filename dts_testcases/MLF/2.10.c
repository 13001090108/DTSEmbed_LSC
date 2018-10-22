#include <stdlib.h>
struct A_2_10 {
       char *p;
};

void setNull_2_10(char * p) {
     p= (char*)malloc(sizeof(char));
}
void callSetNull_2_10(char * a) {
     setNull_2_10(a);
}
int foo_2_10() {
    struct A_2_10 a;
    callSetNull_2_10 (a.p);
    return 0;
}











