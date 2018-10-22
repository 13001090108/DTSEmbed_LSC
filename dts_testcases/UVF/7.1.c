void foo_7_1(int b) {
	int a = b;
}
void call_7_1(int b) {
	foo_7_1(b);
}
int bar_7_1() {
	int b;
	call_7_1(b);
	return 0;
}

// Memory
void fooa_7_1(char *p) {
	*p;
}
void call_7_1(char *p) {
	fooa_7_1(p);
}
int bara_7_1() {
	char *p;
	call_7_1(p);
	return 0;
}
