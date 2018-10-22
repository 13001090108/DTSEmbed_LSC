int * func1_1() 
{
	return (int*)0;
}
void test1_2(int *p)
{
	int a = 0;
	a = *func1_1();//DEFECT, NPD_EXP,func1
}