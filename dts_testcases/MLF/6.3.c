#include <stdlib.h>

struct A_6_3 {
    char *p;
};
struct A_6_3 a_6_3;
void foo_6_3() {
    a_6_3.p = (char*)malloc(sizeof(char));
}
int main_6_3(int argc, char **argv) {
    foo_6_3();
    a_6_3.p = (char*)malloc(sizeof(char));
    return 0;
}






