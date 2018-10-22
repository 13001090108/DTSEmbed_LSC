int g;
//Àı1
int f(int x,int y){
	if(x>0)
		return y++;
	return x+y;
}
int main(){
	int a[10];
	int i=f(5,9);//i=10
	a[i]=0;//OOB
	int j=f(0,9);//j=9
	a[j]=0;//OK
}