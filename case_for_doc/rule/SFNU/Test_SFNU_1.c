//#include<windef.h>
#typedef bool int
#define false 0
#define true 1
static bool static_p(unsigned int);
static bool static_p(unsigned int p_1)
{
	bool ret=false;
	unsigned int i=p_1+1u;
	/*...*/
	if(i==0){
		ret=true;
	}
	return ret;
}

int main(void)
 {
 /*...*/
  return 0;
 }
