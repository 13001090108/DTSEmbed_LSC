int *alloc_5_6() {
	char *p;
	return p;
}
int foo_5_6(int i) {
	if (alloc_5_6() || i) ;
	*alloc_5_6();
	return 0;
}
