#include<setjmp.h>
void f_NSJ_1(jmp_buf mark,unsigned int val) {
     longjmp(mark,val);//NSJ
}
