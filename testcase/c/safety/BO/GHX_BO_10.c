#include <stdio.h>
void wrapped_read(char* buf, int count) 
{
fgets(buf, count, stdin);
}
void ghx_BO_10_f10()
{
char buf1[12];
char buf2[12];
char dst[16];
wrapped_read(buf1, sizeof(buf1));
wrapped_read(buf2, sizeof(buf2));
sprintf(dst, "%s-%s\n", buf1, buf2);//DEFECT
}
