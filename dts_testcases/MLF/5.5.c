#include <stdlib.h>

char *foo_5_5() {
     char *p= (char*)malloc(sizeof(char));
     return p;
}
int fun_5_5(int argc, char **argv) {
    if (argv[1][0] == 'a') ;
    char *q=foo_5_5();
    return 0;
}



