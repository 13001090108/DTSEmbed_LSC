struct A_2_6 {
	int a;
	int b;
	int *p;
};
int foo_2_6(int i) {
	struct A_2_6 a;
	if (i || a.a) ;
	a.b = a.a;
	return 0;
}

// Memory
int bar_2_6(int i) {
	struct A_2_6 a;
	if (i || !a.p) ;
	*a.p = 1;
	return 0;
}
