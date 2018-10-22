
int i = 0;

void f1()
{
	char buf[10];
	buf[i] = 10;
}

void f2()
{
	f1();
}

void f3()
{
	i = 100;
	f2(); //DEFECT
}