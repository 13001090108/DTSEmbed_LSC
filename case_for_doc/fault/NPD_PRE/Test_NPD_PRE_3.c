int* h(){
	return NULL;
}
void g1(int* p){
	if(p==(void*)0&&*p==0){  //FP, NPD
		return;
	}
}
void f(){
	g1(h());//DEFECT, NPD,The 1 Param of function g1
}