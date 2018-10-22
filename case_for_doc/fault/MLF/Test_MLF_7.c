void f(){
	int *memleak_error3,*memleak_error4;
	memleak_error3=(int*)malloc(100);
	memleak_error4=(int*)malloc(10);
	if(!memleak_error3||!memleak_error4){
		return;
	}
}