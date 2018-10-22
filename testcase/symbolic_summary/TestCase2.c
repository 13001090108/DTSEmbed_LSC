int g;
//절1
int f1(int x, int y){
	if(x>0)
		return y++;
	else
		return x+y;
}
int main1(int x,int y){
	int a[5];
	int i=f1(5,3);//i=4
	a[i]=4;//OK
	return 0;
}

//절2
int f2(int x, int y){
	if(x>0)
		return y++;
	else
		return x+y;
}
int main2(int x,int y){
	int a[5];
	int i=f2(5,4);//i=5
	a[i]=4;//OOB
	return 0;
}

//절3
int f3(int x, int y){
	x++;
	if(x>0)
		return y++;
	else
		return x+y;
}
int main3(int x,int y){
	int a[5];
	int i=f3(5,3);//i=4
	a[i]=4;//OK
	return 0;
}

//절４
int f4(int x, int y){
	x++;
	if(x>0)
		return y++;
	else
		return x+y;
}
int main4(int x,int y){
	int a[5];
	int i=f4(0,4);//i=5
	a[i]=5;//OOB
	return 0;
}

//절5
int f5(int x, int y){
	x++;
	if(x>0)
		return y++;
	else
		return x+y;
}
int main5(int x,int y){
	int a[5];
	int i=f5(-1,4);//i=4
	a[i]=5;//OK
	return 0;
}

//절6
int f6(int x, int y){
	x++;
	if(x>0)
		return y++;
	else
		return x+y;
}
int main6(int x,int y){
	int a[5];
	int i=f6(-1,5);//i=5
	a[i]=5;//OOB
	return 0;
}