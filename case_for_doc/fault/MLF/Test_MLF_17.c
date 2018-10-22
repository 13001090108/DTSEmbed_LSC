void f1(){
	int *memleak_error1=(int*)0;
	memleak_error1 = (int *)malloc(4);
	free(memleak_error1);
	free(memleak_error1);//DEFECT, MLF, memleak_error1
}