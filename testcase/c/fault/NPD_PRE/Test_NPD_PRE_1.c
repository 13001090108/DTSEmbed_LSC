#include <stdio.h>
#include <stdlib.h>
#include <string.h>
char *getString()
{
    int a =0;
    if(a)
      return (char *)malloc(sizeof(char)*5);
    else
      return NULL;
    }
int main(int argc, char *argv[])
{
    
    char a[5];
    //char *p = (char *)0;
    strcpy(a, getString());
    return 0;
}
