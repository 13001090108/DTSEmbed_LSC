char *p[10];
void foo_7_5() {
	*p[0] = 'a';
}
void bar_7_5() {
	foo_7_5();
}
int baz_7_5() {
	p[0] = 0;
	bar_7_5();
	//foo_7_5();
	return 0;
}
