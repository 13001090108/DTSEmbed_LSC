#include <stdlib.h>

char *foo_5_9() {
     char *p= (char*)malloc(sizeof(char));
     return p;
}
int fun_5_9(int argc, char **argv) {
    if (*foo_5_9() == 'a') ;
    return 0;
}







