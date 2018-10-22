int foo_1_3(int i) {
	char p;
	if (i || p) {
		p = 'a';
	}
	return 0;
}

// Memory
int bar_1_3(int i) {
	char *p;
	if (i || !p) {
		*p = 'a';
	}
	return 0;
}
