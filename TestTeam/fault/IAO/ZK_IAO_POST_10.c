int func2(int);
int func3();

void func1(int var, int flag)
{
	int i;

	i = var / func2(flag); //DEFECT
}

int func2(int flag)
{
	if (flag < 0) {
		return func3();
	} else {
		return 0;
	}
}

int func3()
{
	return 0;
}