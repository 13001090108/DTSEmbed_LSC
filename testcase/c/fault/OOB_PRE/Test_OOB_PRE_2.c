int f1(int i){
	char buf[10];
	buf[i]=5;
	return 1;
}

int f2(int j){
	j=10;
	f1(j);//FP
	return 2;
}

int f3(){
	int k=9;
	f2(k);
	return 3;
}
