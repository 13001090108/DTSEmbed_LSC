#include<stdio.h>
#include<stdlib.h>
void jhb_npd_25_f1()
{
	FILE *fpout;
	char ch;
	fpout=fopen("file_a.dat","w");
	ch=getchar();
	for(;ch!='#';)
	{
		fputc(ch,fpout);  //DEFECT
		ch=getchar();
	}
	fclose(fpout);
}
