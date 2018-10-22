int func1(int a) {
	int array[4];
	if (a > 4 || a < 0) {
		return 0;
	}
	array[a] = 1;  //DEFECT,OOB,array
}
