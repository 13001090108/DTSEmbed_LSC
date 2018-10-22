int b[5];
void foo_6_5() {
	int a = b[0];
}
int bar_6_5() {
	foo_6_5();
	return 0;
}

// Memory
char *p[5];
void fooa_6_5() {
	*p[0];
}
int bara_6_5() {
	fooa_6_5();
	return 0;
}
