#define MAX 5

void func2(int);
void func3(int, int, int);
void func4(int, int, int);

void func1(int var)
{
	func2(var); //FP
}

void func2(int var)
{
	func3(0, var, 0);
}

void func3(int n, int var, int m)
{
	if (var < 0 || var >= MAX) {
		return;
	} else {
		func4(0, 0, var);
	}
}

void func4(int n, int m, int var)
{
	int array[MAX];

	array[var] = var;
}