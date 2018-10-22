int *alloc_5_2() {
	char *p;
	return p;
}
int foo_5_2() {
	if (!alloc_5_2())
		*alloc_5_2();
	return 0;
}
