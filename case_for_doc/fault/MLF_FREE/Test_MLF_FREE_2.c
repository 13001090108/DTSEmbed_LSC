int * i;
void f(int* p,int flag){
	if(flag)
		i=p;
}
void f1(int flag){
	int*p =(int*)malloc(10);
	f(p,flag);
}