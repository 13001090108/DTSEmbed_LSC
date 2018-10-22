int func2()
{
	int a = 0;
	int b = 10 % a; // DEFECT, IAO, 
	return 0;
}