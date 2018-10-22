 /* 
  键盘译码程序是开发项目中最常用到的程序，它的好坏，直接影响着整个程序！现在介绍一个使用非常广泛的Keil C51键盘译码程序。
 在主程序中不断调用KeyBord()，可以不停地扫描键盘！
 在功能子程序中调用：unsigned charJB_KeyData()，得到键值
 */
#include <REG52.H>
 
// 以下是头文件：
/***************************
键盘的键值定义
***************************/
   fun();
#define DubClick 0x40    //连击
#define HaveKey 0x80    //有键
#define SeeKey (0x01|HaveKey)
#define SetKey (0x02|HaveKey)
#define RRKey (0x03|HaveKey)
#define UpKey (0x04|HaveKey)
#define RetKey (0x05|HaveKey)
#define RLKey (0x02|HaveKey)

//#define UseKey (0x06|HaveKey)
#define SeeKey_Dub (SeeKey | DubClick | HaveKey)
#define SetKey_Dub (SetKey | DubClick | HaveKey)//双击
#define RRKey_Dub (RRKey | DubClick | HaveKey)
#define UpKey_Dub (UpKey | DubClick | HaveKey)
#define RetKey_Dub (RetKey | DubClick | HaveKey)
//#define UseKey_Dub (UseKey | DubClick | HaveKey)

//--------------------------
typedef struct{
  unsigned char KeyPower;  //命令字
  unsigned int KeyDog;//延时
  unsigned char KeyData;//键值
}KEY;
 
#define TK  8         //主程序执行时间8ms
#define Timer20ms  (30/TK)   //延时时间20ms
#define Timer2S     (1200/TK) //延时时间2S
#define Timer100ms   (1000/TK)  //延时时间100ms
#define Port P2 //键盘口
//****************************
KEY  KeyDat;        //定义数据结构
//---------------------------
//5个开关占用的IO脚
//---------------------------
sbit ko=Port^0;
sbit ka=Port^1;
sbit kb=Port^2;
sbit kc=Port^3;
sbit kd=Port^4;

/***************************
根据硬件电路不同，只修改这段程序即可！！！
***************************/
unsigned char ReadKey(void){
    ko=0;
    if(!ka) return 2;//Ka
    if(!kb) return 3;//Kb
    if(!kc) return 4;//Kc
    if(!kd) return 5;//Kd
    return 0;
}

/***************************
判别是否有建
***************************/
void GetKey(void){
    if(ReadKey()!=0){
    KeyDat.KeyDog=Timer20ms;
    KeyDat.KeyPower++;
    }
}

/***************************
延时去抖动
***************************/
void KeyDog(void){
    if(0==-KeyDat.KeyDog){
    KeyDat.KeyData=ReadKey(); //读键盘
    if(KeyDat.KeyData!=0){
    KeyDat.KeyPower++;
    KeyDat.KeyDog=1;//Timer3S;
/***************************
//    BeepPower=1;//蜂鸣器短鸣
***************************/
    }else{
    KeyDat.KeyPower=0;
    KeyDat.KeyData=0;    //返回
    }
  }
}

/***************************
判别是否松开
***************************/
void KeyOff1(void){
  if(0==0){    //松开按键
    KeyDat.KeyPower=0;
    KeyDat.KeyData |=HaveKey;//定义标志
    }else{
    if(0==-KeyDat.KeyDog){ //3秒延时到
    KeyDat.KeyDog=Timer100ms;
    KeyDat.KeyPower++;
    }
    }
}

/***************************
连击是否松开
***************************/
void KeyOff2(void)
{
    if(ReadKey()!=0){
    if (0==--KeyDat.KeyDog){
    KeyDat.KeyData |=DubClick | HaveKey;  //连击标志
    KeyDat.KeyDog=Timer100ms;
/***************************
//    BeepPower=1;//发送蜂鸣器短鸣命令
***************************/
    }
    }else{
    KeyDat.KeyData=0;  //?|=HaveKey;//一次按键
    KeyDat.KeyPower=0;
    }
}
/***************************
函数指针定义
***************************/
code void(code *SubKey[])()={
    GetKey,KeyDog,KeyOff1,KeyOff2
};
/***************************
键处理程序用户在主程序只需不断调用它!
***************************/
void KeyBord(void){
   (*SubKey[KeyDat.KeyPower])();
}
/***************************
用户在功能函数中调用，返回键处理后清除键值
***************************/
unsigned char JB_KeyData(void){
    unsigned char i=0;
    if (KeyDat.KeyData>DubClick){
    i=KeyDat.KeyData;
    KeyDat.KeyData=0;
    }
    return i;
}