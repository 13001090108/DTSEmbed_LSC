void func(int* p, int a)
{
	*p = 1;
} 
void test2(int b){
	int *memleak_error1=NULL;
	memleak_error1=(int*)malloc(sizeof(int)*100);
	if (b > 0) {
		free(memleak_error1);
	}
	func(memleak_error1, 1);//DEFECT, UFM, memleak_error1
}