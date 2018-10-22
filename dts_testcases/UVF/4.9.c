int b[5], a[5];
void f_4_9() {
	b[0] = a[0];
}
int bar_4_9(){
	f_4_9();
	return 0;
}

// Memory
int *p[5];
void alloc_4_9() {
	*p[0] = 1;
}
int foo_4_9() {
	alloc_4_9();
	return 0;
}
