#include <string.h>

void f()
{
     int i=0;
     while(i<10){
     if(i==5)
             break;
	i++;
     }
     char buffer[i];
     strcpy(buffer,"123456");
}
