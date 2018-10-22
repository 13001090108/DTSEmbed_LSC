int *func() {
	return 0;
}
int func1()
{
	int *p;
	p = func();
	*p = 1;  //DEFECT,NPD,p
}