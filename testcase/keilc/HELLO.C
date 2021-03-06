//红外避障电动小车C51程序
#include"reg51.h"
#include<intrins.h>
#define uchar unsigned char
#define uint  unsigned int
#define left_infrare  0
#define right_infrare 1
#define dj_state1        0X5F      //前进
#define dj_state2        0X4F      //右转 
#define dj_state3        0X1F      //左转 
#define dj_state4        0X0F      //后退 
#define dj_state5        0XfF      //停车
#define light_off        0x0f      //关转向灯
#define left_light       0X5F      //左转向灯    两个是5f
#define right_light      0XaF      //右转向灯0xaf，两个是0xbf
#define back_light       0XcF      //刹车灯即后灯
#define front_light      0x3f      //前灯
#define light_on         0xff      //开所有灯
#define true  1
#define false 0
#define LCD_Data  P0
#define Busy  0x80            //用于检测LCD状态字中的Busy标识
sbit    c=P1^2;              //转向灯使能端
uchar code talk1[]={"backward"};
uchar code talk2[]={"forward"};
uchar code talk3[]={"Turnleft"};
uchar code talk4[]={"Turn right"};
uchar flage =0x00;
sbit  ledcs=P1^2;         //74H573的片选信号
//sbit  left_led=P0^2;     //左红外发射管
//sbit  right_led=P0^3;    //右红外发射管

sbit  LCD_RS = P1^5;     //LCD定义引脚
sbit  LCD_RW = P1^6;     //
sbit  LCD_E  = P1^7 ;
void Delay5Ms(void)
{
 uint TempCyc = 5552;
 while(TempCyc--);
}
//400ms延时
void Delay400Ms(void)
{uchar TempCycA = 5;
 uint TempCycB;
 while(TempCycA--)
   { TempCycB=7269;
     while(TempCycB--);
    }
}
//LCD读状态
unsigned char ReadStatusLCD(void)
{
 LCD_Data = 0xFF;
 LCD_RS = 0;
 LCD_RW = 1;
 LCD_E = 0;
 LCD_E = 0;
 LCD_E = 1;
 while (LCD_Data & Busy);   //检测忙信号
 return(LCD_Data);
}
//LCD写数据
void WriteDataLCD(unsigned char WDLCD )
{
 ReadStatusLCD();  //检测忙
 LCD_Data = WDLCD;
 LCD_RS=1;
 LCD_RW =0;
 LCD_E = 0; //若晶振速度太高可以在这后加小的延时
 LCD_E = 0; //延时 ,为了安全
 LCD_E = 0; //延时
 LCD_E = 1;
}
//LCD写指令
void WriteCommandLCD(unsigned char WCLCD,BuysC)
{
 if (BuysC) ReadStatusLCD();   //根据需要检测忙,BuysC为0时忽略忙检测
 LCD_Data = WCLCD;
 LCD_RS= 0;
 LCD_RW= 0;
 LCD_E = 0;  //延时 ,为了安全
 LCD_E = 0;
 LCD_E = 0; //延时
 LCD_E = 1;
}
void LCDInit(void)         //LCD初始化
{
 Delay400Ms();
 LCD_Data = 0;
 WriteCommandLCD(0x38,0);  //三次显示模式设置，不检测忙信号
 Delay5Ms();
 WriteCommandLCD(0x38,0);
 Delay5Ms();
 WriteCommandLCD(0x38,0);
 Delay5Ms();

 WriteCommandLCD(0x38,1); //显示模式设置,开始要求每次检测忙信号
 WriteCommandLCD(0x08,1); //关闭显示
 WriteCommandLCD(0x01,1); //显示清屏
 WriteCommandLCD(0x06,1); // 显示光标移动设置
 WriteCommandLCD(0x0C,1); // 显示开及光标设置
}
//按指定位置显示一个字符
void DisplayOneChar(uchar X, uchar Y, uchar DData)
{
 Y &= 0x1;
 X &= 0xF;                 //限制X不能大于15，Y不能大于1
 if (Y)
 X |= 0x40;               //当要显示第二行时地址码+0x40;
 X |= 0x80;               // 算出LCD的指令码
 WriteCommandLCD(X, 0);   //这里不检测忙信号，发送地址码
 WriteDataLCD(DData);
}
//按指定位置显示一串字符(只能写一行)；
void DisplayListChar(uchar X, uchar Y,uchar ListLength, uchar  *DData,uchar n)
{ uchar i;
 Y &= 0x01;
 X &= 0x0F;                 //限制X不能大于15，Y不能大于1
 for(i=0;i<ListLength;i++)
 { if (X <= 0x0F) //X坐标应小于0xF
    {   DisplayOneChar(X, Y, DData[i]); //显示单个字符
         if(n==true)Delay400Ms();
          X++;
    }
  }
}
/****************************
 红外线接收子程序,利用了中断的下降沿触发方式
****************************/
void infrared_ray()interrupt 0  using 3
{  uchar i=90;
	bit i=1;  
   flage=0x01;             //接受标志位
   while(i--);            //减小灵敏度
   
   EX0=0;             //关掉中断，等到发射方波后才开启，处于别动
}
// 延时子程序

void delay(uint n)
{
  while(--n);
}
//中断初始化
void Init0(void)
{  EA=1;
   IT0=1;
    }
/***************************************
/*原理是把中断打开并 发射方波，
当有中断时就转到中断产生中断位为下一步转向做准备，
当没有是关闭中断
****************************************/
void seng_wave(uchar timer,bit n)//timer通过载波发射信号的时间，n->左右发射管的选择
{  uchar i;
   P1 |= 0X04;      //ledcs=1为74ls573为11脚为高电平时数据直接输出，为低时把数据锁存住，即保持
   IE |= 0X01;
   P0 |=0x0c;   //04
   for(i=timer;i>0;i--)
     { if(n)P0^=0x08;                      // 右发射管通过载波发射信号//00
        else P0^=0x04;                    // 左发射管通过载波发射信号//0c
         delay(100);                     //这里控制着灵敏度（控制38khz的方波的多少）和距离
      }                                     //timer*delay(x)即为发射管得到的平均电流
    P1 &= 0Xfb;
    IE &= 0Xfe;
}
//led转向灯指示子程序
void light_control(uchar deng)
{   ledcs=1;
    P0 =deng;
    ledcs=0;  //11111011
}
//电机和灯光的控制部分
void  control(uchar n,uchar dj_state,uchar light)
{   uchar i;
   // P1|=0x04;
     light_control(light);    //led转向指示灯
     delay(100);
     P2 =dj_state;              //电机的方向控制
    WriteCommandLCD(0x01,1); //LCD显示清屏

          switch(dj_state)
          { case dj_state2 :{ DisplayListChar(3,1,10,talk4,false);}break;
            case dj_state3: { DisplayListChar(3,1,8,talk3,false);}break;
            case dj_state4: { DisplayListChar(3,1,7,talk1,false); }break;
             default :break;
             }
          for(i=n;i>0;i--)
          {delay(2000);}
           P2=dj_state5;               //停车
         light_control(light_off);       //led关闭
        WriteCommandLCD(0x01,1); //LCD显示清屏
         P2=dj_state1;                     //前进
        if(dj_state1)
           { P1|=0X04;          //ledcs=1;
             P0=0x0f;
             P1&=0XFB;
             delay(100);
             DisplayListChar(0,0,7,talk2,false);
             }
     }
/****************************************
避障主要控制部分
*****************************************/
void move_car(void)
 {
   uchar temp =0x00;
   //左边红外管发射
       seng_wave(1,left_infrare);     //向下为中断开启有关闭后，要执行的语句
        if(flage==0x01){temp|=0x01;flage=0x00;}
       //右边红外管发射
         delay(30);
        seng_wave(1,right_infrare);    //向下为中断开启有关闭后，要执行的语句
        if(flage==0x01){temp|=0x02;flage=0x00;}

      //左边有障碍物，右转
     if(temp==0x01){control(2,dj_state2,left_light); temp =0x00;}
      //右边有障碍物，左转
      else if(temp==0x02) {control(2,dj_state3,right_light ); temp =0x00;}
       //两个方向都有障碍物，后退，右转
        else if(temp==0x03) {control(10,dj_state4,back_light );
              control(5,dj_state2,right_light ); temp =0x00;}       

    }
	fun();
void main(void)
{  Init0();       //中断初始化
   P1 |= 0X04;    //开锁存器的控制位
   P0 = 0xFf;     //数据口的清零
   P1&=0XFB;      //关锁存器的控制位
   LCDInit();     //LCD初始化
   WriteCommandLCD(0x01,1);   //显示清屏
   delay(100);
   P2=dj_state1;
   DisplayListChar(0,0,8,talk2,false);
 while(1)
   {    move_car();  //主要控制部分
        delay(200000);//延时
    }
 }