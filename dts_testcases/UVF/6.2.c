int b;
void foo_6_2() {
	int a = b;
}
int bar_6_2() {
	foo_6_2();
	return 0;
}

// Memory
char *p;
void fooa_6_2() {
	*p;
}
int bara_6_2() {
	fooa_6_2();
	return 0;
}
