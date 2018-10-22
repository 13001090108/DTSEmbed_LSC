void test(char *str)
{
	char *p;
	p = strdup(str);
	if(p)
		printf("result: %s\n", p);
	/* there's no free and p is a local variable */
	return;//DEFECT, MLF, p
}