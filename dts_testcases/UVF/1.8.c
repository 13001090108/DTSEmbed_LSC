int foo_1_8(int i) {
	char p;
	p = 'a';
	if (i || p) ;
	return 0;
}

// Memory
int bar_1_8(int i) {
	char *p;
	*p = 'a';
	if (i || p) ;
	return 0;
}
