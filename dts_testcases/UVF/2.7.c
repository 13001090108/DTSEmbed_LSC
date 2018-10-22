struct A_2_7 {
	int a;
	int b;
	int *p;
};
int foo_2_7() {
	struct A_2_7 a;
	a.b = a.a;
	if (a.a) ;
	return 0;
}

// Memory
int bar_2_7() {
	struct A_2_7 a;
	*a.p = 1;
	if (!a.p) ;
	return 0;
}
