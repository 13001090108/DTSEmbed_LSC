int func(int a, double b)
{
	char *s = getenv("ConFig_File");
	fopen(s, "r");
	return 0;
}
