int a = 1;
void func(int* ptr,int b){
	if(a>0)
		ptr[a];
	ptr += b;
	int c = ptr[a];
	int* d = ptr+b;
}
