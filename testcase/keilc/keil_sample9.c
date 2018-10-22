/*************************************************************
红外线遥控器按键检测程序.
通过检测两次下降沿之间的时间差判断接受到的数据位.
已经通过了测试,能够正确区分出32bit数据的遥控器按键键值.
具有数据重发功能,但是数据的重发有点频繁.
使用晶震频率为11.0592MHz,所有定时值都是基于这个频率计算.
占用很少量的CPU时间,使用了外部中断0接受数据,定时器0进行计数,
定时器1作为串口的波特率发生器(Band = 9600).
主函数会使MCU进入低功耗模式,如需加入自己的代码需要屏蔽此功能.
状态机:
    1.如果时间差=0,由空闲态进入接受态
    2.如果时间差>1ms and <1.3ms,收到数据0
    3.如果时间差>2ms and <2.5ms,收到数据1
    4.如果时间差>13.2ms and <13.8ms,收到开始位
    5.如果时间差>12.2ms and <12.8ms,收到停止位(没有检测)
    6.如果时间定时器溢出(时间差>20ms),进入空闲状态
*************************************************************/
//        本程序 可以说是状态机的典范                                       //
//        参照了网友高伟能gwnpeter@21cn.com的代码和思路，仅供学习参考       //
//        如有问题请mailto xuwenjun@21cn.com    欢迎与我交流!               //
//--------------------------------------------------------------------------//
//                                                                          //
//                    (c) Copyright 2001－2003 xuwenjun                     //
//                            All Rights Reserved                           //
//                                    V1.00                                 //
//--------------------------------------------------------------------------//
//标　题: Ir_6222遥控芯片接收程序                                           //
//文件名: ir_6222.c                                                         //
//版　本: V1.00                                                             //
//修改人: 徐文军                         E-mail:xuwenjun@21cn.com           //
//日　期: 03-06-14                                                          //
//描　述: Ir_6222遥控芯片接收程序                                           //
//--------------------------------------------------------------------------//
//老版本: 无                             老版本文件名:                      //
//创建人: 徐文军                         E-mail:xuwenjun@21cn.com           //
//日　期: 03-06-14                                                          //
//描　述: Ir_6222遥控芯片接收程序                                           //
//        当ykok=1时,ykcode中的数据就是接收到的遥控码(14位的最后8位)          //
//--------------------------------------------------------------------------//
//占用以下资源:                                                             //
//        1. 遥控使用外部中断0,接P3.2口                                     //
//        2. 遥控使用定时计数器1                                            //
//        3. 5.1字节data RAM                                                //
//        4. 293字节 code ROM                                               //
//--------------------------------------------------------------------------//
//声　明: 
                                                           //
//        以下代码仅免费提供给学习用途，但引用或修改后必须在文件中声明出处. //
//        如用于商业用途请与作者联系.    E-mail:xuwenjun@21cn.com           //
//              本程序参照了网友高伟能gwnpeter@21cn.com的代码，仅供学习参考       //
//        如有问题请mailto xuwenjun@21cn.com    欢迎与我交流!               //
//--------------------------------------------------------------------------//

#include <REG52.H>
#include "Ir_6222.h"                //  ht6222函数原型: 公用函数
//＃i nclude "xwj_4led.h"                //  四位LED显示模块  //
//＃i nclude    "xwj_pcf8566.h"                         //  I2C总线LCD8566函数声明    //
//＃i nclude <stdio.h>
//--------------------------------------------------------------------------//


#define TIME_0_00MS        0x0000
#define TIME_1_00MS        0x039a
#define TIME_1_13MS        0x0480
#define TIME_2_00MS        0x0733
#define TIME_2_50MS        0x0900
#define TIME_13_2MS        0x2ecd
#define TIME_20_0MS        0x47ff
#define TIME1_LOAD        (0xffff - TIME_20_0MS)

bit running;
long Irbuf;
unsigned char Irdat;
bit Irok;

void IrInit(void)                                                //遥控接收初始化
{
    //-----init TIME1----
    TMOD |= 0x10;                                          //TMOD T0,T1均选用方式1(16位定时)
    TH1    = TIME1_LOAD >> 8;
    TL1    = TIME1_LOAD & 0xff;
//        SCON=0x00;
        IP|=0x01;                                           //SETB  INT0 中断优先
        TCON |= 0x41;                                    //TCON  EX0下降沿触发,启动T1 //
    TR1    = 1;
        IE|=0x89;                                           //SETB        EX0 0x1  外部中断 0 允许
                                                                        //SETB        ET0 0x8  定时器 1 中断允许
                                                                          //SETB        EA  0x80 开中断
}

unsigned char IrGetcode(void)                        //返回遥控码
{
        Irok=0;
        return(Irdat);
}

bit IrTest(void)                                        //检查有无遥控信号
{
        return(Irok);
}

void int0_isr(void) interrupt 0        //遥控使用外部中断0,接P3.2口
{
    unsigned int timer;
   
    TR1 = 0;
    timer = ((TH1 << 8) | TL1) - TIME1_LOAD;
    TH1 = TIME1_LOAD >> 8;
    TL1 = TIME1_LOAD & 0xff;
    TR1 = 1;
   
    if        (timer > TIME_1_00MS && timer < TIME_1_13MS)    //data 0
        Irbuf = (Irbuf << 1) & 0xfffffffe;
    else if    (timer > TIME_2_00MS && timer < TIME_2_50MS)    //data 1
        Irbuf = (Irbuf << 1) | 0x00000001;
    else if    (timer == TIME_0_00MS || timer > TIME_13_2MS)
        Irbuf = 0x0000;
    running = 1;
}

void time1_isr(void) interrupt 3        //遥控使用定时计数器1
{
//    EA = 0;
//    TR1 = 0;
    TH1 = TIME1_LOAD >> 8;
    TL1 = TIME1_LOAD & 0xff;
//    if    ((((Irbuf >> 24) & 0xff) == (~((Irbuf >> 16)) & 0xff)) &&(((Irbuf >> 8) & 0xff) == (~((Irbuf >> 0)) & 0xff)))
    if    (((Irbuf >> 8) & 0xff) == ((~(Irbuf >> 0)) & 0xff))
    {
        Irdat = (Irbuf>>8) & 0xff;
        Irok = 1;
//        pcf8566_showhh(Irdat);
    }
    else if(Irbuf == 0x00 && Irok == 1)
                  ;
//        pcf8566_showhh(Irdat);
    else
        Irok = 0;
//    IE0 = 0;
//    EA = 1;
    running = 0;
}

/*
//  HT6222测试主函数内容
main()
{
        IrInit();
        led_test();                                        //4LED测试函数
        for(;1;)                                                //主程序
        {
                if (IrTest())
                        led_showhh(IrGetcode());
                led_delay(10);
        }
}

*/