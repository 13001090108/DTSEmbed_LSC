int* test4(){
	int *memleak_error1=NULL;
	memleak_error1=(int*)malloc(sizeof(int)*100);
	free(memleak_error1);
	memleak_error1[0] = 1;//DEFECT, UFM, memleak_error1
}