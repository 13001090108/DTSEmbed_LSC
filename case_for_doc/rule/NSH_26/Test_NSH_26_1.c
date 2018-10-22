int func1(int a)
{
	int c = a/10;	
	return c;
}
	
int func2(int a)
{
	int c = a/10;
	if(c<0) c = 0;	
		return c;
}
	
int func3(int a)
{
	int c = a/10;
	if(c<0) c = 0;	
		c=10;	
	return func2(a);
}

int func4(int a)
{
	int c = a/10;
	if(c<0) c = 0;	
	c=10;	
	return c;
}
void func5(int a)
{
	if(a < 0)
		return;
	a = 10;
}