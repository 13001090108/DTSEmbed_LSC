struct A_7_3 {
	char *p;
	char b;
	char a;
};
struct A_7_3 a;

void fooa_7_3() {
	a.a = a.b;
}
void call_7_3() {
	fooa_7_3();
}
int bara_7_3() {
	call_7_3();
	return 0;
}

// Memory
void foo_7_3() {
	*a.p;
}
void call_7_3() {
	foo_7_3();
}
int bar_7_3() {
	call_7_3();
	return 0;
}



