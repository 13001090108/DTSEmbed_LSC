#include <stdlib.h>
int foo_4_5() {
    char *p[10];
    if (p[0]) 
       p[0]=0;
    p[0]= (char*)malloc(sizeof(char));
    return 0;
}








