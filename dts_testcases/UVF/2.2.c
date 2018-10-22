struct A_2_2 {
	int a;
	int b;
	int *p;
};
int foo_2_2() {
	struct A_2_2 a;
	if (a.a)
		a.b = a.a;
	return 0;
}

// Memory
int bar_2_2() {
	struct A_2_2 a;
	if (!a.p)
		*a.p = 1;
	return 0;
}
