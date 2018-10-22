char *p;
void foo_6_2() {
	*p = 'a';
}
int bar_6_2() {
	p = 0;
	foo_6_2();
	return 0;
}
