#include <stdlib.h>
int foo_4_1() {
    char *p[10];
    int i=0;
    for(i=0;i<=9;i++){
        p[i]= (char*)malloc(sizeof(char));
    }
    return 0;
}










