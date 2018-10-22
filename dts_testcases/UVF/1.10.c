int b, a;
void f_1_10() {
	b = a;
}
void callF_1_10() {
	f_1_10();
}
int bar_1_10(){
	callF_1_10();
	return 0;
}

// Memory
int *p;
void alloc_1_10() {
	*p = 1;
}
void callAlloc_1_10() {
	alloc_1_10();
}
int foo_1_10() {
	callAlloc_1_10();
	return 0;
}
