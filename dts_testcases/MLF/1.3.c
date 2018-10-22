#include <stdlib.h>
int foo_1_3(int i) {
    char *p = (char*)malloc(sizeof(char));
    if (i || p)
       return 0;
    free(p);
    return 0;
}


