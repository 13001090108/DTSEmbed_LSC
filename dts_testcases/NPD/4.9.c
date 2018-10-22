int*p[10];
void setNull_4_9() {
	p[0] = 0;
}
int foo_4_9() {
	setNull_4_9();
	*p[0] = 'a';
	return 0;
}
