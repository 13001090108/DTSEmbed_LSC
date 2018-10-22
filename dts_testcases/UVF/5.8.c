int *alloc_5_8() {
	char *p;
	return p;
}
int foo_5_8(int i) {
	*alloc_5_8();
	if (alloc_5_8() || i) ;
	return 0;
}
