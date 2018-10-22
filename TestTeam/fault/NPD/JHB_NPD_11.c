#include <stdlib.h>
#include <stdio.h>
void jhb_npd_11_f1(){
	char a[]="-100";
    char *b;
	b=NULL;
	int c;
	c=atoi(a)+atoi(b);  //DEFECT
	printf("c=%d\n",c);
}
void jhb_npd_11_f2()
{
	char a[]="-100";
	char b[]="456";
	int c;
	c=atoi(a)+atoi(b);  //FT
	printf("c=%d\n",c);
}
