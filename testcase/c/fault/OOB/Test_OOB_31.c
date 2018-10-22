int main()
{
	int a[10];
	a[10] = 1;  //DEFECT,OOB,a
	return 0;
}
