int f1(int i){
	char buf[10];
	buf[i]=5;
	return 1;
}

int f2(int j){
	f1(5);f1(j);
	return 2;
}

int f3(){
	int k=10;
	f2(k);//FP,OOB_PRE
	return 3;
}
