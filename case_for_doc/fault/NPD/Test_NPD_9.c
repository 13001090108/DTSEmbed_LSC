int *g(){
	return 0;
}
int f2(){
	int *t=g();
	if(1>0 && *t>0){ //DEFECT,NPD, t
		return false;
	}
}
