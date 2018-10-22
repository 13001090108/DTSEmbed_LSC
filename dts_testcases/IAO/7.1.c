void foo_7_1(int p) {
	10 % p;
}
void bar_7_1(int p) {
	foo_7_1(p);
}
int ff_7_1() {
	int p = 0;
	//foo_7_1(p);
	bar_7_1(p);
	return 0;
}
