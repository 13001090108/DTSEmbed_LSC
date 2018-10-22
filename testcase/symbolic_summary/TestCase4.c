int f(int x,int y){
	return (x*y);
}
int main(int m,int n){
	int i=f(m+2,n);
	return i;
}
int g(int a,int b){
	int array[20];
	int j=main(8,2);
	a[j]=0;//oob
	return 0;
}