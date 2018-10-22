#include<setjmp.h>
void func(jmp_buf mark,unsigned int val) {
	longjmp(mark,val);
}
