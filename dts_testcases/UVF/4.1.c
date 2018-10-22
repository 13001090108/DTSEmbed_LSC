int foo_4_1() {
	int a[5], b[5];
	b[0] = a[0];
	return 0;
}

// Memory
int bar_4_1() {
	int *p[5];
	*p[0] = 1;
	return 0;
}
