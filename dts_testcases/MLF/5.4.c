#include <stdlib.h>

char *foo_5_4() {
     char *p= (char*)malloc(sizeof(char));
     return p;

}
int fun_5_4(int argc, char **argv) {
    if (argv[1][0] == 'a')
       if (argv[1][1] == 'b')
          char* q=foo_5_4();
    return 0;
}



