int get(){
	int a = 10;
	return a;
}
int get1(int a){
	return a*10;
}
void fun(){
	float f; 
	int i; 
	f = (float)i;
	double d = get1(i);
	d = get();
}
