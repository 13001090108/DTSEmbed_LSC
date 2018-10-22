struct A_6_3 {
	char *p;
	char b;
	char a;
};
struct A_6_3 a;

void fooa_6_3() {
	a.a = a.b;
}
int bara_6_3() {
	fooa_6_3();
	return 0;
}

// Memory
void foo_6_3() {
	*a.p;
}
int bar_6_3() {
	foo_6_3();
	return 0;
}



