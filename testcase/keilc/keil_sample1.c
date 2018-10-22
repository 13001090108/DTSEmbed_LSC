//-----------------------函数声明，变量定义--------------------------------------------------------
#include <reg51.h>
#include <intrins.h>
#include<ABSACC.H>  
//-----------------------定义管脚--------------------------------------------------------
sbit PWM=P1^0;             //PWM波形输出
sbit DR=P1^1;              //方向控制
#define  timer_data  (256-100) //定时器预置值,12M时钟是，定时0.1ms
#define  PWM_T 100         //定义PWM的周期T为10ms
unsigned char PWM_t;       //PWM_t为脉冲宽度(0~100)时间为0~10ms
unsigned char PWM_count;   //输出PWM周期计数
unsigned char time_count;  //定时计数
bit direction;             //方向标志为
//--------------------------------------------------------------------------------------------------
// 函数名称：timer_init
// 函数功能：初始化设施定时器
//--------------------------------------------------------------------------------------------------
void timer_init()
     {
   TMOD=0x22; /*定时器1为工作模式2(8位自动重装)，0为模式2(8位自动重装) */
      PCON=0x00;
      TF0=0;
      TH0=timer_data;   //保证定时时长为0.1ms
      TL0=TH0;
      ET0=1;
   TR0=1;            //开始计数
      EA=1;             //中断允许
   }
//--------------------------------------------------------------------------------------------------
// 函数名称：setting_PWM
// 函数功能：设置PWM的脉冲宽度和设定方向
//--------------------------------------------------------------------------------------------------
void setting_PWM()
      {
   if(PWM_count==0)  //初始设置
   {
   PWM_t=20;
   direction=1;
   }
   }
//--------------------------------------------------------------------------------------------------
// 函数名称：IntTimer0
// 函数功能：定时器中断处理程序
//--------------------------------------------------------------------------------------------------
void IntTimer0() interrupt 1
              {
     time_count++;
              DR=direction;
     if(time_count>=PWM_T)
              {
     time_count=0;
     PWM_count++;
     setting_PWM();  //每输出一个PWM波调用一次
     }
     if(time_count<PWM_t)
     PWM=1;
     else
     PWM=0;
     }
//--------------------------------------------------------------------------------------------------
// 函数名称：main
// 用户主函数
// 函数功能：主函数
//--------------------------------------------------------------------------------------------------
void main()
     {
  timer_init();
  setting_PWM();
  }