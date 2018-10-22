#include <stdlib.h>
struct A_2_4 {
       char *p;
};
int foo_2_4 (int i, int j) {
    struct A_2_4 a;
    a.p=(char*)malloc(sizeof(char));
    if (i)
       *a.p='a';
    if(j){
       *a.p='b';
       free(a.p);
    }
    return 0;
}











