void f3()
{
	int j;
	int m;
	m += 1; //DEFECT, UVF, m
	j++; //DEFECT, UVF, j
}
