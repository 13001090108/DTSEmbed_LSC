int func1()
{
	int a = 0;
	div(10, a); // DEFECT, IAO_PRE, 
	return 0;
}