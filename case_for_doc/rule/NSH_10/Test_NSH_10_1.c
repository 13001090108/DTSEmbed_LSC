void func(int a)
{
	int b = 0;
	for(int i = 0;i < a;i++)
		{
			b++;
			if(b > 10) 
			break;
			else 
			continue;
		}
	while(b > 0){
		 b--;
		if(b==1) break;
		else return;
	 }
	do{
	b++;
	 if(b > 0) 
	 break;
		}while(true);
}
