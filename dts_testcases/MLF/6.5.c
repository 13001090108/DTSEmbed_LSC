#include <stdlib.h>

char *p_6_5[10];
void foo_6_5() {
    p_6_5[0] =(char*)malloc(sizeof(char));
}
int main_6_5(int argc, char **argv) {
    foo_6_5();
    p_6_5[0] =(char*)malloc(sizeof(char));
    return 0;
}






