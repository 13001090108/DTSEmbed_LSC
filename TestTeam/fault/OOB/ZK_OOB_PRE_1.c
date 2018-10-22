#define MAX 5

int g_array[MAX];

void func2(int);
void func3(int, int, int);

void func1()
{
	int i;

	i = MAX;
	func2(i); 
}

void func2(int var)
{
	if (var < MAX) {
		g_array[var] = var;
	} else {
		func3(0, 0, var);//DEFECT
	}
}

void func3(int n, int m, int var)
{
	g_array[var] = var;
}