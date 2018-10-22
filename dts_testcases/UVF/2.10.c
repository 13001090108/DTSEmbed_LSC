struct A_2_10 {
	int a;
	int b;
	int *p;
};
struct A_2_10 a;
void f_2_10() {
	a.b = a.a;
}
void callF_2_10() {
	f_2_10();
}
int bar_2_10(){
	callF_2_10();
	return 0;
}

// Memory
void alloc_2_10() {
	*a.p = 1;
}
void callAlloc_2_10() {
	alloc_2_10();
}
int foo_2_10() {
	callAlloc_2_10();
	return 0;
}
