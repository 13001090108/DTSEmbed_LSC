#include <stdlib.h>

char *p_6_2;
void foo_6_2() {
    p_6_2 =(char*)malloc(sizeof(char));
}
int main_6_2(int argc, char **argv) {
    foo_6_2();
    p_6_2 =(char*)malloc(sizeof(char));
    return 0;
}





