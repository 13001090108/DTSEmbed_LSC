int func3()
{
	double a = -1.0;
	double b = log(a); // DEFECT, IAO_PRE, 
	return 0;
}