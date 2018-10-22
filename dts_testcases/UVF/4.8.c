int foo_4_8(int i) {
	char p[5];
	p[0] = 'a';
	if (i || p[0]) ;
	return 0;
}

// Memory
int bar_4_8(int i) {
	char *p[5];
	*p[0] = 'a';
	if (i || p[0]) ;
	return 0;
}
