int foo_1_7() {
	char p;
	p = 'a';
	if (p) ;
	return 0;
}

// Memory
int bar_1_7() {
	char *p;
	*p = 'a';
	if (p) ;
	return 0;
}
