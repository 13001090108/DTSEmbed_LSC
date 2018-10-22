#typedef bool int
#define false 0
#define true 1
void static_p(unsigned int p_1)
{
	unsigned int static_p;
	bool c_1=false;
	/*...*/
	if(c_1){
		unsigned int static_p=1u;
		 /*...*/
		static_p=static_p+1u;
	}else {
		static_p=p_1;
	}
	/*...*/
}
