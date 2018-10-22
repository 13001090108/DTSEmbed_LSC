void fun2(int *p){

		delete p;

}
void fun3(int *p){
	fun2(p);
}

void f(int flag){
	int *p=new int;
	

	fun3(p);   //FP
}