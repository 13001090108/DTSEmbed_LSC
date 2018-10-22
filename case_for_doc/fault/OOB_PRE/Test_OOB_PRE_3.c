#define MAX 5
typedef struct {
	int index;
	int array[MAX];
} ST;
void func2(int, ST);
void func1(ST var)
{
	if (var.index >= 0 && var.index < MAX) {
		return;
	} else {
		func2(0, var); //DEFECT
	}
}
void func2(int n, ST var)
{
	var.array[var.index] = var.index;
}