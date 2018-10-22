
int * func1_1() 
{
	int * p = (void *)0;
	return p;
}
void test1_2(int *p)
{
	int a = 0;
	a = *func1_1();//DEFECT, NPD_EXP,func1_1
}
