#typedef bool int
#define false 0
#define true 1
void foo(unsigned int p_x){}
void static_p(void)
{
	unsigned int x=1u;
	unsigned int y=2u;
	bool flag=false;
	/*...*/
	if(flag==false)
	{
		 x++;
	}
	x=x+y++;
	foo(x++);
}
