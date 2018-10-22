#include <stdlib.h>

char *foo_5_3() {
    char *p= (char*)malloc(sizeof(char));
    return p;
}
int bar_5_3(int i) {
    if (i ==1 || i == 2)
       char*q=foo_5_3();
       return 0;
}



