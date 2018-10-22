int* p;
void f(int a)
{
	if(!p)
		a++;
	*p = a+5;
}