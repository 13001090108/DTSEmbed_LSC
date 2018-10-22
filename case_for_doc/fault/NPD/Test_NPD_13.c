void f(){
	g(h());  //DEFECT,NPD,The 1 Param of function g
}
void g(int* p){
	int a=*p;  //FP,NPD
}
int* h(){
	return 0;
}