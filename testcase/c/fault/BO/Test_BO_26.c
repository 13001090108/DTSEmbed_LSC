#include <string.h>
int a;void f(){a=11;}
void f1(){
f();char buffer[10];
strncat(buffer,"1234567890",a);
}
