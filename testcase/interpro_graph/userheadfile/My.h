#include <stdio.h>
#include <string.h>
int length;
void print(char *str)
{
	if(str!=NULL)
		{
			length=strlen(str);
			printf("The length of String \" %s \" is %d .\n",str,length);
		}
	else
		{
			printf("The String is NULL!\n");
		}
}