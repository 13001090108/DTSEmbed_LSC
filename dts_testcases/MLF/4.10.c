#include <stdlib.h>
char *p[10]={0};
void fun_4_10() {
     p[0] = (char*)malloc(sizeof(char));
}
void function_4_10() {
     fun_4_10();
}
int foo_4_10() {
    function_4_10();
    return 0;
}


