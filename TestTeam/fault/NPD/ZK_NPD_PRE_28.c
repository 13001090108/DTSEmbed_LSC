void func3(int *var)
{
	*var = 1;
}

void func2(int *var)
{
	func3(var);
}


void func1(bool flag)
{
	int *ptr = 0;

	if (flag) {
		ptr = new int;
	}

	func2(ptr); //DEFECT
}