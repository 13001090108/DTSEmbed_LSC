#define ZERO 0

void func2(bool, int&, int);

void func1(int var, bool flag)
{
	int val;

	func2(flag, val, var);
	val = var % val; //DEFECT
}

void func2(bool flag, int &var1, int var2)
{
	if (flag) {
		var1 = ZERO * var2;
	} else {
		var1 = ZERO / var2;
	}
}