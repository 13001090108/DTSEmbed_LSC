#include <string.h>

int f1(){
    int a=3,b;
    if(a==3) b=9;
    else b=10;
    return b;
}
void f2(){
     int a;
     a=f1();
     char buffer[9];
     //strcpy(buffer,\"1234567890\");
     strncat(buffer,"1234567890",a);
}
