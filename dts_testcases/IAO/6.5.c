int p[10];
void foo_6_5() {
	10 % p[0];
}
int ff_6_5() {
	p[0] = 0;
	foo_6_5();
	return 0;
}
