int b;
void foo_8_2(int c) {
	int a = c;
}
int bar_8_2() {
	foo_8_2(b);
	return 0;
}

// Memory
char *p;
void fooa_8_2(char *q) {
	*q;
}
int bara_8_2() {
	fooa_8_2(p);
	return 0;
}
