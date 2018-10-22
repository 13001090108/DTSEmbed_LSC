struct A_2_11 {
	int a;
	int b;
	int *p;
};
int foo_2_11() {
	struct A_2_11 a;
	if (a.a != 'a') ;
	return 0;
}

// Memory
int bar_2_11() {
	struct A_2_11 a;
	if (*a.p != 'a') ;
	return 0;
}
