int* h(){
	return NULL;
}
void g2(int* p){
	if(!p&&*p==0){  //FP, NPD
		return;
	}
}
void f(){
	g2(h());//DEFECT, NPD,The 1 Param of function g2
}