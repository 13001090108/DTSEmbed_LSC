int foo_1_5() {
	char p;
	if (p) ;
	p = 'a';
	return 0;
}

// Memory
int bar_1_5() {
	char *p;
	if (p) ;
	*p = 'a';
	return 0;
}
