extern int f2();
extern int f3();

int f1(){
	return 1;
}
int main(){
	f1();
	f2();
	f3();
	printf("%d\n",f3());
	return 0;
}