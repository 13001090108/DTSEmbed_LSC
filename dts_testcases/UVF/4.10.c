int b[5], a[5];
void f_4_10() {
	b[0] = a[0];
}
void callF_4_10() {
	f_4_10();
}
int bar_4_10(){
	callF_4_10();
	return 0;
}

// Memory
int *p[5];
void alloc_4_10() {
	*p[0] = 1;
}
void callAlloc_4_10() {
	alloc_4_10();
}
int foo_4_10() {
	callAlloc_4_10();
	return 0;
}
