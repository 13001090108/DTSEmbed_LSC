int *alloc_5_3() {
	char *p;
	return p;
}
int foo_5_3(int i) {
	if (!alloc_5_3() || i)
		*alloc_5_3();
	return 0;
}
