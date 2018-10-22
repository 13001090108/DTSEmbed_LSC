//class A{
//	void foo();
//};
//void A::foo()
void foo()
{
	int *ptr;
	ptr = (int*)malloc(sizeof(int));
	free(ptr);
}
void func(){
	foo();
}