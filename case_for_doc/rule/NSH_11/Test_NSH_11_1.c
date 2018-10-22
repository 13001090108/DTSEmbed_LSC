int a = 0;
int c = 1;
int b = (a = 1,c=9);
int get(){return 1;}
void func()
{
	for(int i=0,j=0;i<10&&j<10;i++,j++)
	{
		b = (a=i,c=j);
		int w=4,r = 9;
		a = b,c=8;
		 double d = (double)get(),f = (double)c;
		 d = (double)a;
	}
	int i,j;
	for(i=0,j=0;i<10&&j<10;i++,j++)
	{
		(a=0,j=0);
		b = (a=i,c=j);
		int w=4,r = 9;
		 a = b,c=8;
		 double d = (double)get(),f = (double)c;
		 d = (double)a;
	}
}
