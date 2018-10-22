int func2()
{
	int a = 0;
	ldiv(10, a); // DEFECT, IAO_PRE, 
	return 0;
}