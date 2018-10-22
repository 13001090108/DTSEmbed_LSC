#include <stdlib.h>
#include <string.h>

#define BUFSIZE 2

int main(int argc, char *argv[])
{
	char *buf;

	buf = (char *)malloc(BUFSIZE);
	if (buf == NULL)
		return -1;
	strcpy(buf, argv[1]); //DEFECT
	free(buf);
	return 0;
}