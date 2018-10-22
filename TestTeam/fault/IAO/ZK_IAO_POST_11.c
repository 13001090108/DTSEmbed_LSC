#define ZERO 0

void func2(int&, int);

void func1(int var)
{
	int val;

	func2(val, var);
	val = var / val; //DEFECT
}

void func2(int &var1, int var2)
{
	var1 = ZERO * var2;
}