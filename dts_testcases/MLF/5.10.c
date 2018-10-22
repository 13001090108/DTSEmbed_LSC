#include <stdlib.h>

char *foo_5_10() {
     char *p= (char*)malloc(sizeof(char));
     return p;
}
int fun_5_10(int argc, char **argv) {
    if (argv[1][0] == 'a' && *foo_5_10() == 'a');
    return 0;
}








