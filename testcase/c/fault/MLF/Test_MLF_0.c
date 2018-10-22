#include<stdlib.h>
char * xmalloc()
{
    char *mem;
     mem = (char *)calloc(10, 1);
   return mem;
}
int main()
{
    char *p;
    p=xmalloc();
    return 0;
}
