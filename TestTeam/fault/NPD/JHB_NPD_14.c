#include <stdlib.h>
#include <string.h>
#include <stdio.h>
int jhb_npd_14_f1(void)
{
	char *str = NULL;
	str = (char*)calloc(10, sizeof(char));
	strcpy(str, "Hello");         //DEFECT
	printf("String is %s\n", str);
	free(str);
	return 0;
}
