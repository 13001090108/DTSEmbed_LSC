
void f1(int i)
{
	char buf[4];
	buf[i] = 1;
}

void f2(int j)
{
	f1(j);
}

void f3(int k)
{
	f2(k);
}

void f4()
{
	f3(5); //DEFECT
}