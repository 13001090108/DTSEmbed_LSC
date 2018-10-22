int flag;
void fun2(int *p){
        if(p)
		   delete p;

}

void f(){
	int *p=new int;
	fun2(p);
}