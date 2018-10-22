
void fun(int i)
{
	char buf[4];
	buf[i] = 'c';
}

void func()
{
	int i = 10;
	fun(i); //DEFECT
}