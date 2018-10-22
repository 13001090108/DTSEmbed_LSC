#include <stdio.h>

void f_NSC (unsigned int n)
{
	unsigned int u = n;
	if(u<0){// NSC,defect
	    printf("one");
	}else{
	    printf("two");
	}
	//...
}
