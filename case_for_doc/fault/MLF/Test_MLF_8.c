int func2(int c)
{
	char *p;
	p = (char *)malloc(sizeof (char) * 2);
	if (p == (void*)0)
		return 1;
	p = (void*)0;//DEFECT, MLF, p
	free((char *)(p));
	return 1;
}
