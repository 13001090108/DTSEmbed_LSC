int test1(int level)
{
	int* x = NULL;
	int p = 0;
	if (level>0) {
		x=&p;
	}
	if (level<4)
		return *x; //DEFECT,NPD,x
	return 0;
}