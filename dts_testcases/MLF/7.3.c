#include <stdlib.h>

struct A_7_3 {
    char *p;
};
struct A_7_3 a_7_3;
void foo_7_3() {
    a_7_3.p =(char*)malloc(sizeof(char));
}
void bar_7_3() {
    foo_7_3();
}
int main_7_3(int argc, char **argv) {
    bar_7_3();
    a_7_3.p =(char*)malloc(sizeof(char));
    return 0;
}

