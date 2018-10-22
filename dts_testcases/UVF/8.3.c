struct A_8_3 {
	char *p;
	int b;
	int a;
};
struct A_8_3 a;

void fooa_8_3(int b) {
	int a = b;
}
int bara_8_3() {
	fooa_8_3(a.b);
	return 0;
}

// Memory
void foo_8_3(char *p) {
	*p;
}
int bar_8_3() {
	foo_8_3(a.p);
	return 0;
}



