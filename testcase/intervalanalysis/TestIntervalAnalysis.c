int t1=3;
char c1;
int f(int k){
	t1=4;
	t1*=5;
    int i=1;
	if (k>0)
	   i=10;
	else 
	   i=1;
	   
	k=10;
	
	while(k-->0)
	{
		i++;
	}
	
	switch(k)
	{
		case 0:
			k=20;
			break;
		case 1:
			k=30;
			break;
	}
	
	do{
		i++;
	}while(k>15);
	
	for(;i<50;i++)
	{
		k++;
	}
	   
	return i;
}
