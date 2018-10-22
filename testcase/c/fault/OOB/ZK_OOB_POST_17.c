#define MAX 5

int g_val = 0;

void func2(int);

void func1(int var)
{
	int array[MAX];

	func2(var);

	array[g_val] = g_val; //DEFECT
}

void func2(int var)
{
	if (var >= MAX) {
		g_val = var + 1;
	} else if (var < 0) {
		g_val = var;
	} else {
		g_val = -var;
	}
}
