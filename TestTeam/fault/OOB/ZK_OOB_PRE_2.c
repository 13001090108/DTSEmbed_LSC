#define MAX 5

int g_array[MAX][MAX];

void func2(int);
void func3(int, int, int);

void func1()
{
	int i;

	i = MAX;
	func2(i); //
}

void func2(int var)
{
	if (var < MAX) {
		g_array[0][var] = var;
	} else {
		func3(0, var, 0);//DEFECT
	}
}

void func3(int n, int var, int m)
{
	g_array[var][var] = var;
}