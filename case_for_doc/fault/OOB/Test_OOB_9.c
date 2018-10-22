int func2(int a) {
	int array[4];
	if (a>=0 && a<=4) {
		array[a] = 1;  //DEFECT,OOB,array
	}
	return 0;
}