int *p;
void f1()
{
	p = (int *)malloc(4);
}
void f2()
{
	p = (int *)malloc(4);
	f1();
}