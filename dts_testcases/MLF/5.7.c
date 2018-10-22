#include <stdlib.h>

char *foo_5_7() {
     char *p= (char*)malloc(sizeof(char));
     return p;

}
int fun_5_7(int argc, char **argv) {
     char* q=foo_5_7();
     return 0;
     if (argv[1][0] == 'a') ;   
}




