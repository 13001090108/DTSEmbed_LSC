int foo_5_4() {
	return 0;
}
int ff_5_4(int i, int j) {
	if (i)
		foo_5_4();
	if (j)
		10 % foo_5_4();
	return 0;
}
