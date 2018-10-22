int foo_4_5() {
	char p[5];
	if (p[0]) ;
	p[0] = 'a';
	return 0;
}

// Memory
int bar_4_5() {
	char *p[5];
	if (p[0]) ;
	*p[0] = 'a';
	return 0;
}
