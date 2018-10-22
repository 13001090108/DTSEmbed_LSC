char *foo_5_4() {
	return 0;
}
int bar_5_4(int i, int j) {
	if (i)
		foo_5_4();
	if (j)
		*foo_5_4();
	return 0;
}
