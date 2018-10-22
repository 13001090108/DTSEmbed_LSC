#include <string.h>

int all=7;
void f3(){
     all=8;
     }
void f4(){
     char buffer[8];
     f3();
     strncat(buffer,"123456789",all);
}
