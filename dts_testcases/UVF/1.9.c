int b, a;
void f_1_9() {
	b = a;
}
int bar_1_9(){
	f_1_9();
	return 0;
}

// Memory
int *p;
void alloc_1_9() {
	*p = 1;
}
int foo_1_9() {
	alloc_1_9();
	return 0;
}
