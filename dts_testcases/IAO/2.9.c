struct A_2_9 {
	int a;
};
struct A_2_9 a;
void setZero_2_9() {
	a.a = 0;
}
int ff_2_9() {
	a.a = 1;
	setZero_2_9();
	10 % a.a;
	return 0;
}
