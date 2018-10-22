int count=0;

void f1(int i)
{
	f2();
	f3(30);
	if(count++<10)
		f1(5);
}
int f2()
{
	f3(30);
}
int f3(int c)
{
	printf("hello from f2()!	count=%d\n",count);
	return 33;
}

int main()
{
	f1(1);
	return 0;
}