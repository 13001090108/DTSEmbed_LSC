#include <stdlib.h>

char *p_7_2;
void foo_7_2() {
    p_7_2 =(char*)malloc(sizeof(char));
}
void bar_7_2 () {
    foo_7_2 ();
}
int main_7_2 (int argc, char **argv) {
    bar_7_2();
    p_7_2 =(char*)malloc(sizeof(char));
    return 0;
}
