void test(char *str)
{
	char *p;
	p = strdup(str);
	if(p) {
		printf("result: %s\n", p);
		free(p);
		free(p);			//DEFECT, MLF, p
	}
}