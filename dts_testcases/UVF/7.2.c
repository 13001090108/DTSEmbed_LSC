int b;
void foo_7_2() {
	int a = b;
}
void call_7_2() {
	foo_7_2();
}
int bar_7_2() {
	call_7_2();
	return 0;
}

// Memory
char *p;
void fooa_7_2() {
	*p;
}
void call_7_2() {
	fooa_7_2();
}
int bara_7_2() {
	call_7_2();
	return 0;
}
