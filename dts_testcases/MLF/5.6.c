#include <stdlib.h>

char *foo_5_6() {
     char *p= (char*)malloc(sizeof(char));
     return p;
}
int fun_5_6(int argc, char **argv) {
    if (argv[1][0] == 'a' && argv[1][1] == 'b') ;
    char *q=foo_5_6();
    return 0;
}




