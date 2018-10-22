void foo(unsigned int p_1)
{
/*...*/
}
void static_p(unsigned int p_1)
{
	static unsigned int type0=0u;
	static unsigned int type1=1u;
	/*...*/
	(p_1==0)?foo(type0): foo(type1);
}
