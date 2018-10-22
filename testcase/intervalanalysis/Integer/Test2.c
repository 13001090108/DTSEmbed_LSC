#include <stdio.h>

int test1(){
	int i,j=0;
	for (i = 0 ; i < 10 ; ++i) {
        ++j;
    }
	printf("i=%d,j=%d\n",i,j);  //10 10
	return 0;
}


int test2(){
	int i,j,k;
	k = 0;
	j = 10;
	for (i = 0 ; i < j ; ++i) {
        ++k;
    }
    if (k==10) {
        i += j;
    }
	printf("i=%d,j=%d,k=%d\n",i,j,k); //20 10 10
	return 0;
}

int test3(){
	int a=1,b=2,c=3;
	int result=0;
	if(a>0){
		result=a*b*c;	printf("result=%d ",result); //6
	}else{
		result=a;	printf("result=%d ",result);
	}
	int* p=(int*)malloc(sizeof(int));
	result++;	printf("result=%d ",result);  //7
	result=(a+b)/c;	printf("result=%d ",result);  //1
	result--;	printf("result=%d ",result);  //0
	if(result>0){
		*p=result;	printf("result=%d ",result);
	}else{
		*p=result++;	printf("result=%d ",result); //1
	}
	int* p2=&result;	printf("result=%d ",result);//1
	if(p==p2){
		result+=10;	printf("result=%d ",result);
	}else{
		result-=10;	printf("result=%d ",result); //-9
	}
	if(result<0){
		result=-result;	printf("result=%d ",result); //9
	}else{
		result++;	printf("result=%d ",result);
	}
	result%=4;	printf("result=%d ",result); //1
	int d=21,e=-8,f=-5,g=8,h=5;
	result=d/e;	printf("result=%d ",result); //-2
	result=d/f;	printf("result=%d ",result);//-4
	result=d/g;	printf("result=%d ",result);//2
	result=d/h;	printf("result=%d ",result);//4
	result=d%e;	printf("result=%d ",result);//5
	result=d%f;	printf("result=%d ",result);//1
	result=d%g;	printf("result=%d ",result);//5
	result=d%h;	printf("result=%d ",result);//1
	result=-d/e;	printf("result=%d ",result); //2	
	result=-d%e;	printf("result=%d ",result); //-5
	printf("\n");
	return result;
}

int main(){
	test1();
	test2();
	test3();
	system("pause");
	return 0;
}