void fun1()
{
	int a;
	a = 0;
}

void fun2()
{
	fun1();
}

void fun3()
{
	fun2();
}
	
void fun4()
{
	fun3();
}

void fun5()
{
	fun3();
}

void fun6()
{
	fun5();
	fun4();
}

void fun7()
{
	fun6();
}

void fun8()
{
	fun7();
}