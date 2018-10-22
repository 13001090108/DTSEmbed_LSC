int func5(int *a){
	*a = 1;
	return 0;
}
int main()
{
	int a = 1;
	int* p;
	p = NULL;
	func5(p);  //DEFECT, NPD,p
	return 0;
}