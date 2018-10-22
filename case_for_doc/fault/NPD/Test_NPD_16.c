int *p;
void f1()
{
	p = 0;
}
void f2()
{
	f1();
	*p = 5;     
}