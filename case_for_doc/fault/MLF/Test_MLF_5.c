void f(int a,int b){
	int *memleak_error;
	memleak_error=(int*)malloc(sizeof(int)*100);
	if(a>0){
	if(!memleak_error){
		return;
	}
	if(b<0){
		goto end;
	}
	}
	free(memleak_error);
	end:
	return;
}