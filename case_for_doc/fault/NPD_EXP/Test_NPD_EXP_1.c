int * func1_1() 
{
	return (int*)0;
}
void test1_1(int *p)
{
	int a = 0;
	if (p) {
		a = 1;
	}
	*(p+1) = 1;//NPD_EXP
}