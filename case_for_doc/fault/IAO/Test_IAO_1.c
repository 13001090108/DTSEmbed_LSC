int test1(int a) {
	if(a<10 && a>-1){
		int result=10/a; // DEFECT, IAO, 
	}
}