int foo_5_2() {
	return 0;
}
int bar_5_2() {
	if (foo_5_2())
		10 % foo_5_2();
	return 0;
}
