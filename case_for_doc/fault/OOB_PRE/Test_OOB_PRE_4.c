#define MAX 5
void func1();
void func2(int*);
void func1()
{
	int array[MAX];
	func3(array); //DEFECT
}
void func2(int* ptr)
{
	*(ptr + 10) = 0; //DEFECT
}