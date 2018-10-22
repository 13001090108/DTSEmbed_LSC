struct A_2_9 {
	int a;
	int b;
	int *p;
};
struct A_2_9 a;
void f_2_9() {
	a.b = a.a;
}
int bar_2_9(){
	f_2_9();
	return 0;
}

// Memory
void alloc_2_9() {
	*a.p = 1;
}
int foo_2_9() {
	alloc_2_9();
	return 0;
}
