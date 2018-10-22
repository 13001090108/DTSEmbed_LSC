#include <stdlib.h>

char *p_7_5[10];
void foo_7_5() {
    p_7_5[0] = (char*)malloc(sizeof(char));
}
void bar_7_5() {
    foo_7_5();
}
int main_7_5 (int argc, char **argv) {
    bar_7_5 ();
    p_7_5[0] = (char*)malloc(sizeof(char));
    return 0;
}

