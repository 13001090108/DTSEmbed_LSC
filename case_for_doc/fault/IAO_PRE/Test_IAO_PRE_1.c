#define int 1
int func2(bool, int, int);
int func3(int, int);
void func1(bool flag, int a, int b)
{
	if (a > 2 && a < 10) {
		func2(flag, a, b);
	} else {
		func2(flag, a, b); //DEFECT
	}
}
int func2(bool flag, int var1, int var2)
{
	if (flag) {
		return var2 % var1;
	} else {
		return func3(var1, var2);
	}
}
int func3(int var1, int var2)
{
	var2 /= var1;
	return var2;
}