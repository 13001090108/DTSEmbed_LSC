extern f();
int main(){
	int i=f();
	printf("%d\n",i);
	int array[5];
	array[i]=10;
	return 0;
}