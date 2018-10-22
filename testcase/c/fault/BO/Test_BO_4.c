#include <stdio.h>

void f1()
{
	char buffer1[10]="welcome",buffer2[10]="tochina",buffer3[15];
	sprintf(buffer3,"%6s%s",buffer1,buffer2);
	sprintf(buffer3,"%7d%8d",123,345);//DECFECT
	sprintf(buffer3,"%s%8s",buffer1,buffer2);//DECFECT
}


void f2(char *q){
     char buffer[10],buffer1[11]="1234567890";
     char *p=buffer1;
     sprintf(buffer,"%s","1234567890");//DECFECT
     sprintf(buffer,"%s",p);//DECFECT
     sprintf(buffer,"%s",buffer1);//DECFECT
     sprintf(buffer,"%s",q);//DECFECT
}
