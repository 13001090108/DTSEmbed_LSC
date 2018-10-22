void test1(int b){
	int *memleak_error1=NULL;
	memleak_error1=(int*)malloc(sizeof(int)*100);
	if (b > 0) {
		free(memleak_error1);
	}
	*memleak_error1 = 1;//DEFECT, UFM, memleak_error1
}