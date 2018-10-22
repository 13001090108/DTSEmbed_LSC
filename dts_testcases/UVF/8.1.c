void foo_8_1(int b) {
	int a = b;
}
int bar_8_1() {
	int b;
	foo_8_1(b);
	return 0;
}

// Memory
void fooa_8_1(char *p) {
	*p;
}
int bara_8_1() {
	char *p;
	fooa_8_1(p);
	return 0;
}
