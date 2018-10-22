void foo_6_1(char *p) {
	*p = 'a';
}
int bar_6_1() {
	char *p = 0;
	foo_6_1(p);
	return 0;
}
