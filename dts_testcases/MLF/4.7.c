#include <stdlib.h>
int foo_4_7() {
    char* p[10];
    int i=0;
    for(i=0;i<=9;i++)
        p[i]= (char*)malloc(sizeof(char));
    if (!p[0]) ;
    return 0;
}








