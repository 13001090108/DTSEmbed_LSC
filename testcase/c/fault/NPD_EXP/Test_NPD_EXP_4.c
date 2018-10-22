void test1_1(int *p)
{
	int a = 0;
	if (p) {
		a = 1;
	}
	*(p+1) = 1;//DEFECT, NPD_EXP,p+1
}
