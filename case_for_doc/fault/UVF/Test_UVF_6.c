void test3(int i){
	int value;
	if(i==1)
		value=1;
	if(i==2)
		value=2;
	if(i==3)
		value=3;
	if(i<4)
		value++;  //DEFECT, UVF, value
}