int **p;
int ** get()
{
	int a = 10;
	int *b = a;
	return &b;
}
void fun(int **t)
{
	int a = 10;
	int *b =&a;
	*t = b;
	 a = **t;
	 b = *(get());
}
