int main()
{
	int i=0,*q ;
q= (int *)calloc(16);
	if(*q > 0)  //DEFECT,NPD,q
	{
		i = 0;
	}
	return i;
}
