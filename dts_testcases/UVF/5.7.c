int *alloc_5_7() {
	char *p;
	return p;
}
int foo_5_7() {
	*alloc_5_7();
	if (alloc_5_7()) ;
	return 0;
}
