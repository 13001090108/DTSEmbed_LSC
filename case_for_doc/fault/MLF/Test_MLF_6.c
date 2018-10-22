void f(int a){
	int *memleak_error;
	memleak_error=(int*)malloc(sizeof(int)*100);
	if(a<0||!memleak_error)return;
	free(memleak_error);
}