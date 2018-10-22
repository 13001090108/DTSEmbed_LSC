#define BUFSIZE 20

void zk_bo_8_f1(char *str)
{
	char buf[BUFSIZE];
	char *ptr;

	ptr = buf;
	while (*ptr++ = *str++) //DEFECT
		continue;
	return;
}