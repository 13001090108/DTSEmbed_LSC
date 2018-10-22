struct A_2_12 {
	int a;
	int b;
	int *p;
};
int foo_2_12(int i) {
	struct A_2_12 a;
	if (i || a.a != 'a') ;
	return 0;
}

// Memory
int bar_2_12(int i) {
	struct A_2_12 a;
	if (i || *a.p != 'a') ;
	return 0;
}
