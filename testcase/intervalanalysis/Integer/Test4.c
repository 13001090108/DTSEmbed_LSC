int global;

int test2() {
	global = 14;
	return 0;
}

int test1(){
	int result=10;
	return result;
}

int main(){
	int a=test1();
	test2();
	int b;
	b = global;
	return 0;
}
