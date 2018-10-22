void f2(){
	int *memleak_error1;
	memleak_error1 = (int *)malloc(8);
	free(memleak_error1);
	free(memleak_error1);//DEFECT,MLF, memleak_error1
}