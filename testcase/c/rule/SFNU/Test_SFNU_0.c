static int static_p(unsigned int);
static int static_p(unsigned int p_1)
{
	int ret=0;
	unsigned int i=p_1+1u;
	/*...*/
	if(i==0){
		ret=1;
	}
	return ret;
}

int main(void)
{
	/*...*/
	return 0;
}
