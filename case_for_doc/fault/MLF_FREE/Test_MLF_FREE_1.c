void my_free(char *p, int flag) {
	if (flag == 17) {
		p = 0;
		return;
	}
	if(flag == 34){
		return;
	}
	free(p);
}
void foo(){
	int *ptr;
	ptr = (int*)malloc(sizeof(int));
	my_free(ptr,1);
}