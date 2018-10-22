int *alloc_5_5() {
	char *p;
	return p;
}
int foo_5_5() {
	if (alloc_5_5()) ;
	*alloc_5_5();
	return 0;
}
