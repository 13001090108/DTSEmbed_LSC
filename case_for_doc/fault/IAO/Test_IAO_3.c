int func3()
{
	int a = 0, b = 10;
	b /= a; // DEFECT, IAO, 
	return 0;
}