#include <stdlib.h>
int foo_1_4(int i, int j) {
    char *p = (char*)malloc(sizeof(char));
    if (i)
        free(p);
    if(j)
         return 0;
    return 0;
}



