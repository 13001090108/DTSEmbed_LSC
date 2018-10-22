void f(int* p,int* q){
	if(q!=(void*)0){
		return;
	}
	if(p==q){
		int b;
	}
	int a=*p;	//DEFECT,NPD,p
}