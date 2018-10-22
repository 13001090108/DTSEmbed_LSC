int* test5(){
	int *memleak_error1=NULL;
	memleak_error1=(int*)malloc(sizeof(int)*100);
	free(memleak_error1);
	int *p;
	p = memleak_error1 + 1;//DEFECT, UFM, memleak_error1
}