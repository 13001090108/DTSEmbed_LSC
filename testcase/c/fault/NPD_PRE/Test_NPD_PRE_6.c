
int func5(int *a){
	*a = 1;  //FP,NPD
	return 0;
}
int main()
{
	int a = 1;
	int* p;
	p = (void*)0;
	func5(p); //DEFECT,NPD,p
	return 0;
}
