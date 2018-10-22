#pragma DB OE CD
#include <reg51.h>
#include <stdio.h>
void main(void)
{
	SCOn=0x50;
	TMOD=0x20;
	TH1=0xf3;
	Tri=1;
	TI=1;

	printf("Hello,world \n");

	while(1) { }
}