int foo_1_12(int i) {
	char p;
	if (i || p != 'a') ;
	return 0;
}

// Memory
int bar_1_12(int i) {
	char *p;
	if (i || *p != 'a') ;
	return 0;
}
