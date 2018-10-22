#include <stdio.h>
#include <process.h>
int main()
{
char buf[5];
scanf("%s", buf);
execl(buf, buf, "hello", NULL);
return 0;
}
