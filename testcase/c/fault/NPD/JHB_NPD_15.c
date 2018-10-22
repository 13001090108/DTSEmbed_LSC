#include <stdio.h>
int jhb_npd_15_f1(void)
{
	FILE *fp;
	char ch;
	fp = fopen("DUMMY.FIL", "w");
	ch = fgetc(fp);
	printf("%c\n",ch);
	clearerr(fp);      //DEFECT
	fclose(fp);
	return 0;
}
