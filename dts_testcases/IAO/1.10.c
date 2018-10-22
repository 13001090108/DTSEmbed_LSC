int a;
void setZero_1_10() {
	a = 0;
}
void foo_1_10() {
	setZero_1_10();
}
int ff_1_10() {
	//setZero_1_10(&a);
	foo_1_10();
	10 % a;
	return 0;
}
