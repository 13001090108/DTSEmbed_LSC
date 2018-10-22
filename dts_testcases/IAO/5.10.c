int foo_5_10() {
	return 0;
}
int ff_5_10(int i) {
	if (i && 10 % foo_5_10() == 0) {
		// do something
	}
	return 0;
}
