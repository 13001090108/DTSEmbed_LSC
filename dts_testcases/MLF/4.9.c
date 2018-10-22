#include <stdlib.h>
char*p[10]={0};
void fun_4_9() {
     p[0] = (char*)malloc(sizeof(char));
}
int foo_4_9() {
    fun_4_9();
    return 0;
}



