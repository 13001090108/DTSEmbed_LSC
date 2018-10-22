char *foo_5_10() {
	return 0;
}
int bar_5_10(int i) {
	if (i && *foo_5_10() == 'a') {
		// do something
	}
	return 0;
}
