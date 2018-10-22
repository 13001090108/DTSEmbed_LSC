#include <string.h>

void f()
{
     int i=0;
     for(;i<10;i++){
     if(i==5)
             break;
     }
     char buffer[i];
     strcpy(buffer,"123456");
}
