struct A_2_8 {
	int a;
	int b;
	int *p;
};
int foo_2_8(int i) {
	struct A_2_8 a;
	a.b = a.a;
	if (i || a.a) ;
	return 0;
}

// Memory
int bar_2_8(int i) {
	struct A_2_8 a;
	*a.p = 1;
	if (i || !a.p) ;
	return 0;
}
