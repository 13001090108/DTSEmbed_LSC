int*p;
void setNull_1_9() {
	p = 0;
}
int foo_1_9() {
	setNull_1_9();
	*p = 'a';
	return 0;
}
