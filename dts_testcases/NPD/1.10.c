int*p;
void setNull_1_10() {
	p = 0;
}
void callSetNull_1_10() {
	setNull_1_10();
}
int foo_1_10() {
	callSetNull_1_10();
	*p = 'a';
	return 0;
}
