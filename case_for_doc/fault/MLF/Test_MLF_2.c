void foo()
{
	int *ptr = (int *)malloc(4);
	*ptr = 25;
	ptr = (int *)malloc(4);
	*ptr = 35;
}
void func(){
	void foo();
}
