#include <stdlib.h>

void foo_7_1(char *p) {
    p =(char*)malloc(sizeof(char));
}
void bar_7_1(char *p) {
     foo_7_1(p);
}
int main_7_1(int argc, char **argv) {
    char *p = 0;
    bar_7_1(p);
    return 0;
}




