#include <string.h>
int main(int argc, char *argv[])
{
	char buf[10];
	/*  BAD  */
	strcpy(buf, "AAAAAAAAAAAAAAAAA");
	return 0;
}