#define MAX 5

int func2(bool);
int func3(int);

void func1(bool flag)
{
	int array[MAX];
	int val;

	val = func2(flag);
	array[val] = val; //DEFECT
}

int func2(bool flag)
{
	if (flag) {
		return MAX;
	} else {
		return func3(MAX);
	}
}

int func3(int var)
{
	return -var;
}