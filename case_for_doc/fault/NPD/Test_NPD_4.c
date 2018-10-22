int main()
{
	int i=0,*p = 0, *q = 0, *a = 0;
	int j = (p == 0)? i: *p;
	if(i != 0 || *q > 0)  //DEFECT,NPD,q
	{
		j = 0;
	}
	return 0;
}