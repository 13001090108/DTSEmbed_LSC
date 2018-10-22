//절1
int g1;
int f1(int x, int y){
	return x+y+g1;
}
int main1(int x,int y){
	int a[5];
	g1=1;
	int i=f1(4,0);//i=5
	a[i]=4;//OOB
	return 0;
}

//절2
int g2;
int f2(int x, int y){
	return x+y+g2;
}
int main2(int x,int y){
	int a[5];
	g2=1;
	int i=f2(3,0);//i=4
	a[i]=4;//OK
	return 0;
}

//절3
int g3;
int f3(int x, int y){
	return x+y+g3;
}
int main3(int x,int y){
	int a[5];
	int i=f3(3,0);//i=3+G
	a[i]=4;//OK
	return 0;
}

//절４
int g4;
int f4(int x, int y){
	g4=1;
	return x+y+g4;
}
int main4(int x,int y){
	int a[5];
	int i=f4(3,1);//i=5
	a[i]=4;//OOB
	return 0;
}