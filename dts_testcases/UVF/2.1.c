struct A_2_1 {
	int a;
	int b;
	int *p;
};
int foo_2_1() {
	struct A_2_1 a;
	a.b = a.a;
	return 0;
}

// Memory
int bar_2_1() {
	struct A_2_1 a;
	*a.p = 1;
	return 0;
}
