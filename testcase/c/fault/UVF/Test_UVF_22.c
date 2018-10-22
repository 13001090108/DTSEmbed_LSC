int fun()
{
	int i,k,j;
	for(i=12;i<10;i++)//条件不符合，不会进入for循环，k没有初始化，但是结果OK
	{
		//break;
		k=i;
	}
	j=k;
}
