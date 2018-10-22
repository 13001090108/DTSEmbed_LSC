void func2(int&, int&);
int func3(int, int);

void func1()
{
	int a, b;

	func2(a, b);
	func3(a, b); //DEFECT
}

void func2(int &var1, int &var2)
{
	var1 = 0;
	var2 = 10;
}

int func3(int var1, int var2)
{
	return (var2 / var1);
}