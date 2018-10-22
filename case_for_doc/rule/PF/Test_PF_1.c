void func(int a , int b) {}
	void func2() {
	void (*proc_pointer)(int a, int b) = func;  
	proc_pointer(1,2);
}
