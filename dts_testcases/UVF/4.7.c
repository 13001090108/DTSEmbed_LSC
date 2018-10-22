int foo_4_7() {
	char p[5];
	p[0] = 'a';
	if (p[0]) ;
	return 0;
}

// Memory
int bar_4_7() {
	char *p[5];
	*p[0] = 'a';
	if (p[0]) ;
	return 0;
}
