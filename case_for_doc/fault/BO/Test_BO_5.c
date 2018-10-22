#include <string.h>
#include <stdio.h>
int main(int argc, char *argv[])
{
	char source[10];
	int i;
	strcpy(source, "0123456789");
	char *dest = (char *)malloc(strlen(source));
	for (i=1;i<=11;i++)
		dest[i] = source[i];
	dest[i] = '\0';
	printf("dest = %s\n", dest);
	return 0;
}