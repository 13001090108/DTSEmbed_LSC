#include <stdlib.h>

char *foo_5_2() {
    char *p= (char*)malloc(sizeof(char));
    return p;
}
int bar_5_2(int i) {
    if (i)
       char* q=foo_5_2();
    return 0;
}


