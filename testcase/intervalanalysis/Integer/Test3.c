#include <stdio.h>

typedef struct st{
	int i;
	char ch;
} st;

int test1(){
	st* p=(st*)malloc(sizeof(st));
	int a=p->i=5; printf("a=%d ",a);   //5
	char a2=p->ch='a'; printf("a2=%c ",a2);
	st p2;
	int b=p2.i=10; printf("b=%d ",b);  //10
	char b2=p2.ch='b'; printf("b2=%c ",b2); 
	int result=0;
	result=a&b; 	printf("result=%d ",result);  //0
	result=a^b;		printf("result=%d ",result);  //15
	result=a|b;		printf("result=%d ",result);  //15
	result=a<<2;	printf("result=%d ",result);  //20
	result=a>>2;	printf("result=%d ",result); //1
	result=a2&b2;	printf("result=%d ",result); //96
	result=a2^b2;	printf("result=%d ",result); //3
	result=a2|b2;	printf("result=%d ",result);  //99
	result=a2<<2;	printf("result=%d ",result);  //388
	result=a2>>2;	printf("result=%d ",result);  //24
	result=result>=0?result+1:-result; 	printf("result=%d ",result); //25
	result=sizeof(p);	printf("result=%d ",result); //4
	result=sizeof(p2);	printf("result=%d ",result); //8
	return result;
}

int main(){
	int a=test1();printf("a=%d ",a);  //8
	system("pause");
	return 0;
}