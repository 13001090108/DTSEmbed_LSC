void func4()
{
	int* p;
	int* a = 0;
	p = a;
	p[0] = 1;  //DEFECT,NPD,p
}
