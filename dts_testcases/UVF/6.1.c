void foo_6_1(int b) {
	int a = b;
}
int bar_6_1() {
	int b;
	foo_6_1(b);
	return 0;
}

// Memory
void fooa_6_1(char *p) {
	*p;
}
int bara_6_1() {
	char *p;
	fooa_6_1(p);
	return 0;
}
