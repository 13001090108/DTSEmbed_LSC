int b[5];
void foo_7_5() {
	int a = b[0];
}
void call_7_5() {
	foo_7_5();
}
int bar_7_5() {
	call_7_5();
	return 0;
}

// Memory
char *p[5];
void fooa_7_5() {
	*p[0];
}
void call_7_5() {
	fooa_7_5();
}
int bara_7_5() {
	call_7_5();
	return 0;
}
