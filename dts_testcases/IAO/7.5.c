int p[10];
void foo_7_5() {
	10 % p[0];
}
void bar_7_5() {
	foo_7_5();
}
int ff_7_5() {
	p[0] = 0;
	bar_7_5();
	//foo_7_5();
	return 0;
}
