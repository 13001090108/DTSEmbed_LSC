
#line 1 "keil_sample8.c" /0




 


 
  
#line 1 "C:\KEIL\C51\INC\REG51.H" /0






 
 
 
 
 
 
 sfr P0   = 0x80;
 sfr P1   = 0x90;
 sfr P2   = 0xA0;
 sfr P3   = 0xB0;
 sfr PSW  = 0xD0;
 sfr ACC  = 0xE0;
 sfr B    = 0xF0;
 sfr SP   = 0x81;
 sfr DPL  = 0x82;
 sfr DPH  = 0x83;
 sfr PCON = 0x87;
 sfr TCON = 0x88;
 sfr TMOD = 0x89;
 sfr TL0  = 0x8A;
 sfr TL1  = 0x8B;
 sfr TH0  = 0x8C;
 sfr TH1  = 0x8D;
 sfr IE   = 0xA8;
 sfr IP   = 0xB8;
 sfr SCON = 0x98;
 sfr SBUF = 0x99;
 
 
 
 
 sbit CY   = 0xD7;
 sbit AC   = 0xD6;
 sbit F0   = 0xD5;
 sbit RS1  = 0xD4;
 sbit RS0  = 0xD3;
 sbit OV   = 0xD2;
 sbit P    = 0xD0;
 
 
 sbit TF1  = 0x8F;
 sbit TR1  = 0x8E;
 sbit TF0  = 0x8D;
 sbit TR0  = 0x8C;
 sbit IE1  = 0x8B;
 sbit IT1  = 0x8A;
 sbit IE0  = 0x89;
 sbit IT0  = 0x88;
 
 
 sbit EA   = 0xAF;
 sbit ES   = 0xAC;
 sbit ET1  = 0xAB;
 sbit EX1  = 0xAA;
 sbit ET0  = 0xA9;
 sbit EX0  = 0xA8;
 
 
 sbit PS   = 0xBC;
 sbit PT1  = 0xBB;
 sbit PX1  = 0xBA;
 sbit PT0  = 0xB9;
 sbit PX0  = 0xB8;
 
 
 sbit RD   = 0xB7;
 sbit WR   = 0xB6;
 sbit T1   = 0xB5;
 sbit T0   = 0xB4;
 sbit INT1 = 0xB3;
 sbit INT0 = 0xB2;
 sbit TXD  = 0xB1;
 sbit RXD  = 0xB0;
 
 
 sbit SM0  = 0x9F;
 sbit SM1  = 0x9E;
 sbit SM2  = 0x9D;
 sbit REN  = 0x9C;
 sbit TB8  = 0x9B;
 sbit RB8  = 0x9A;
 sbit TI   = 0x99;
 sbit RI   = 0x98;
 
 
#line 9 "keil_sample8.c" /0
 
  
#line 1 "C:\KEIL\C51\INC\INTRINS.H" /0






 
 
 
 
 
 extern void          _nop_     (void);
 extern bit           _testbit_ (bit);
 extern unsigned char _cror_    (unsigned char, unsigned char);
 extern unsigned int  _iror_    (unsigned int,  unsigned char);
 extern unsigned long _lror_    (unsigned long, unsigned char);
 extern unsigned char _crol_    (unsigned char, unsigned char);
 extern unsigned int  _irol_    (unsigned int,  unsigned char);
 extern unsigned long _lrol_    (unsigned long, unsigned char);
 extern unsigned char _chkfloat_(float);
 extern void          _push_    (unsigned char _sfr);
 extern void          _pop_     (unsigned char _sfr);
 
 
 
#line 10 "keil_sample8.c" /0
 




 
 
 
 
 
 
 
 sbit dip1=P1^0;
 sbit dip2=P1^1;
 sbit dip3=P1^2;
 sbit dip4=P1^3;
 sbit dip6=P0^4;





 
 void high46(void)
 {
  dip3=1;
  dip2=1; _nop_();
  dip2=0;_nop_();
 }
 void low46(void)
 {
  dip3=0;
  dip2=1;_nop_();
  dip2=0;_nop_();
 }
 void wd46(unsigned char dd)
 {
 unsigned char i;
 for (i=0;i<8;i++)
 {
 if (dd>=0x80) high46();
 else low46();
 dd=dd<<1;
 }
 }
 unsigned char rd46(void)
 {
 unsigned char i,dd;
  dip4=1;
 for (i=0;i<8;i++)
 {
 dd<<=1;
  dip2=1;_nop_();
  dip2=0;_nop_();
 if (dip4) dd|=1;
 }
 return(dd);
 }




 
 
 
 
 
 
 
 sbit dip3=P1^0;
 sbit dip4=P1^1;
 sbit dip5=P1^2;
 sbit dip6=P1^3;





 
 void high46a(void)
 {
  dip5=1;
  dip4=1;_nop_();
  dip4=0;_nop_();
 }
 void low46a(void)
 {
  dip5=0;
  dip4=1;_nop_();
  dip4=0;
 _nop_();
 }
 void wd46a(unsigned char dd)
 {
 unsigned char i;
 for (i=0;i<8;i++)
 {
 if (dd>=0x80) high46a();
 else low46a();
 dd=dd<<1;
 }
 }
 unsigned char rd46a(void)
 {
 unsigned char i,dd;
  dip6=1;
 for (i=0;i<8;i++)
 {
 dd<<=1;
  dip4=1;_nop_();
  dip4=0;_nop_();
 if (dip6) dd|=1;
 }
 return(dd);
 }




 
 void ewen46(void)
 {
 _nop_();
  dip1=1;
 high46();
 wd46(0x30);
  dip1=0;
 }
 unsigned int read93c46_word(unsigned char address)
 {
 unsigned int dat;
 unsigned char dat0,dat1;
  dip7=0;
  dip5=0;
  dip1=dip2=0;
  dip6=1;
  dip1=1;_nop_();
 address=address>>1;
 address=address|0x80;
 address=address|0x80;
 high46();
 wd46(address);
 dat1=rd46();
 dat0=rd46();
  dip1=0;
 dat=dat1*256+dat0;
 return(dat);
 }
 bit write93c46_word(unsigned char address,unsigned int dat)
 {
 unsigned char e,temp=address;
 e=0;
 while (e<3)
 {
  dip7=0;
  dip5=0;
  dip1=dip2=0;
  dip6=1;
  dip1=1;
 ewen46();
 _nop_();
  dip1=1;
 _nop_();
 high46();
 address|=0x80;
 address>>=1; 
 address|=0x40;
 wd46(address);
 wd46(dat/256);
 wd46(dat%256);
  dip1=0;
 _nop_();
  dip1=1;
 time=0;dip4=1;
 while (1)
 {
 if (dip4==1) break;
 if (time>20) break;
 }
  dip1=0;
 if (read93c46_word(temp)==dat)
 {
 return(0);
 }
 e++;
 }
 return(1);
 }




 
 void ewen57(void)
 {
 _nop_();
  dip1=1;
 dip7=0;
 high46();
 low46();
 wd46(0x60);
  dip1=0;
 }
 unsigned int read93c57_word(unsigned int address)
 {
 unsigned int dat;
 unsigned char dat0,dat1;
  dip5=0;
  dip1=dip2=0;
  dip6=1;
  dip1=1;
 address=address>>1;
 high46();
 high46();
 wd46(address);
 dat1=rd46();
 dat0=rd46();
  dip1=0;
 dat=dat1*256+dat0;
 return(dat);
 }
 bit write93c57_word(unsigned int address,unsigned int dat)
 {
 unsigned char e;
 unsigned int temp=address;
 e=0;
 while (e<3)
 {
  dip5=0;
  dip1=dip2=0;
  dip6=1;
  dip1=1;
 ewen57();
  dip1=1;
 _nop_();
 high46();
 low46();
 address>>=1;
 address|=0x80;
 wd46(address);
 wd46(dat/256);
 wd46(dat%256);
  dip1=0;
 _nop_();
  dip1=1;
 time=0;
  dip4=1;
 while (1)
 {
 if (dip4==1) break;
 if (time>20) break;
 }
  dip1=0;
 if (read93c57_word(temp)==dat)
 {
 return(0);
 }
 e++;
 }
 return(1);
 }




 
 void ewen56(void)
 {
 _nop_();
  dip1=1;
 high46();
 low46();
 low46();
 wd46(0xc0);
  dip1=0;
 }
 unsigned int read93c56_word(unsigned char address)
 {
 unsigned int dat;
 unsigned char dat0,dat1;
  dip5=0;
  dip1=dip2=0;
  dip6=1;
  dip1=1;
 address=address>>1;
 high46();
 high46();
 low46();
 wd46(address);
 dat1=rd46();
 dat0=rd46();
  dip1=0;
 dat=dat1*256+dat0;
 return(dat);
 }
 bit write93c56_word(unsigned char address,unsigned int dat)
 {
 unsigned char e;
 unsigned int temp=address;
 e=0;
 while (e<3)
 {
  dip5=0;
  dip1=dip2=0;
  dip6=1;
  dip1=1;
 ewen56();
 _nop_();
  dip1=1;
 _nop_();
 high46();
 low46();
 high46();
 address>>=1;
 wd46(address);
 wd46(dat/256);
 wd46(dat%256);
  dip1=0;
 _nop_();
  dip1=1;
 TH0=0;
 time=0;
  dip4=1;
 while (1)
 {
 if (dip4==1) break;
 if (time) break;
 }
  dip1=0;
 if (read93c56_word(temp)==dat)
 {
 return(0);
 }
 e++;
 }
 return(1);
 }




 
 void ewen76(void)
 {
 _nop_();
  dip1=1;
 dip7=1;
 high46();
 low46();
 low46();
 high46();
 high46();
 wd46(0xff);
  dip1=0;
 }
 unsigned int read93c76_word(unsigned int address)
 {
 unsigned char dat0,dat1;
  dip5=0;
  dip1=dip2=0;
  dip6=1;
  dip1=1;
 address>>=1;
 high46();
 high46();
 low46();
 if((address&0x200)==0x200) high46();
 else low46();
 if ((address&0x100)==0x100) high46();
 else low46();
 wd46(address);
 dat1=rd46();
 dat0=rd46();
  dip1=0;
 return(dat1*256|dat0);
 }
 bit write93c76_word(unsigned int address,unsigned int dat)
 {
 unsigned char e;
 unsigned int temp=address;
 e=0;
 address>>=1;
 while (e<3)
 {
  dip5=0;
  dip1=dip2=0;
  dip6=1;
  dip1=1;
 ewen76();
 _nop_();
  dip1=1;
 high46();
 low46();
 high46();
 if((address&0x200)==0x200) high46();
 else low46();
 if ((address&0x100)==0x100) high46();
 else low46();
 wd46(address);
 wd46(dat/256);
 wd46(dat%256);
  dip1=0;_nop_();dip1=1;
 time=0;dip4=1;
 while (1)
 {
 if (dip4==1) break;
 if (time>10) break;
 }
  dip1=0;
 e++;
 }
 return(1);
 }




 
 main()
 { bit b;
 unsigned int i;
 unsigned int j[32],k;
 for(i=0;i<32;i++)
 j[i]=read93c56_word(i);
 for(i=0;i<32;i++)
 write93c56_word(i,0x0909);
 i=0;
 b=write93c56_word(i,0x0909);
 j[i]=read93c56_word(i);
 i=1;
 b=write93c56_word(i,0x1111);
 j[i]=read93c56_word(i);
 i=2;
 b=write93c56_word(i,0x2222);
 j[i]=read93c56_word(i);
 }
