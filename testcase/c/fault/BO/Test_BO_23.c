#include <string.h>
void f()
{
     int i=10,j=0;
     if(i<8)
            j++;
     if(i>=8)
             i=(j==1?10:9);
     char  buffer[i];
     strcpy(buffer,"123456789");
}
