struct A_2_10 {
	int a;
};
struct A_2_10 a;
void setZero_2_10() {
	a.a = 0;
}
void foo_2_10() {
	setZero_2_10();
}
int ff_2_10() {
	a.a = 1;
	//setZero_2_10(&a);
	foo_2_10();
	10 % a.a;
	return 0;
}
