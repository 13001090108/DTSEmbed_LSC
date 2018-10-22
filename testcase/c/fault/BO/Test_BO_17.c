#include <string.h>

int f1(){
    int a=3,b;
    if(a==3) b=10;
    else b=9;
    return b;
}
void f2(){
     int a;
     a=f1();
     char buffer[a];
     strcpy(buffer,"1234567890");
     //strncat(buffer,\"1234567890\",a);
}
