int p;
void foo_7_2() {
	10 % p;
}
void bar_7_2() {
	foo_7_2();
}
int ff_7_2() {
	p = 0;
	bar_7_2();
	//foo_7_2();
	return 0;
}
