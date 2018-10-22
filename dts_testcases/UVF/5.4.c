int *alloc_5_4() {
	char *p;
	return p;
}
int bar_5_4(int i, int j) {
	if (i)
		alloc_5_4();
	if (j)
		*alloc_5_4();
	return 0;
}
