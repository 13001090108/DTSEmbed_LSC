int b[5];
void foo_8_5(int c) {
	int a = c;
}
int bar_8_5() {
	foo_8_5(b[0]);
	return 0;
}

// Memory
char *p[5];
void fooa_8_5(char *q) {
	*q;
}
int bara_8_5() {
	fooa_8_5(p[0]);
	return 0;
}
