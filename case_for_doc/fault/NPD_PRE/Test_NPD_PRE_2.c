int func5(int *a){
	*a = 1;
	return 0;
}
int func6(int* b) {
	return func5(b);
}
int main()
{
	int a = 1;
	int* p;
	p = NULL;
	func6(p);  //DEFECT, NPD,p
	return 0;
}