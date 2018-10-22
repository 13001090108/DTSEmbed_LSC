int foo_5_3() {
	return 0;
}
int ff_5_3(int i) {
	if (i && foo_5_3())
		10 % foo_5_3();
	return 0;
}
