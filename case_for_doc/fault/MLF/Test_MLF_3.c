void f(){
	int *memleak_error;
	memleak_error=(int*)malloc(sizeof(int)*100);
}