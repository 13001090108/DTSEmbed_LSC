/* 以下为AT24C01～AT24C256的读写程序，各人可根据自己的需要应用。
在buf1中填入需要写入的内容，buf2的大小可根据需要定义。
addr可根据使用的芯片选择，可从任何位置读写，只要在该芯片的范围内。
enumer=ATxxx，根据使用的芯片赋值。各函数中的形式参数不需改变。
本程序只要在调用的程序中定义实际参数即可，下述各子程序不必改动。*/

#include <reg52.h>
#include <intrins.h>
#define  ERROR 10     //允许ERROR的最大次数      
sbit     SDA=P3^0;
sbit     SCL=P3^1;
enum  eepromtype {AT2401,AT2402,AT2404,AT2408,AT2416,AT2432,AT2464,AT24128,AT24256};/*器件的型号*/
enum  eepromtype enumer;   //定义一个枚举变量
unsigned char code buf1 []={1,3,5,7,9,10,11,12,13,15}; /* 发送缓冲区 */
unsigned char buf2 [10]; /* 接收缓冲区 */

/* 一个通用的24C01－24C256共9种EEPROM的字节读写操作程序，
此程序有五个入口条件，分别为读写数据缓冲区指针,
进行读写的字节数，EEPROM首址，EEPROM控制字节，
以及EEPROM类型。此程序结构性良好，具有极好的容错性，程序机器码也不多:
DataBuff为读写数据输入／输出缓冲区的首址
Length 为要读写数据的字节数量
Addr 为EEPROM的片内地址 AT24256为0～32767
Control 为EEPROM的控制字节，具体形式为(1)(0)(1)(0)(A2)(A1)(A0)(R/W),其中R/W=1,
表示读操作,R/W=0为写操作,A2,A1,A0为EEPROM的页选或片选地址;
enumer为枚举变量,需为AT2401至AT24256中的一种,分别对应AT24C01至AT24C256;
函数返回值为一个位变量，若返回1表示此次操作失效，0表示操作成功;
ERROR为允许最大次数，若出现ERRORCOUNT次操作失效后，则函数中止操作，并返回1
SDA和SCL由用户自定义，这里暂定义为P3^0和P3^1; */
/*对于1K位，2K位，4K位，8K位，16K位芯片采用一个8位长的字节地址码，对于32K位以上
的采用2个8位长的字节地址码直接寻址，而4K位，8K位，16K位配合页面地址来寻址*/

/* －－－－－  AT24C01～AT24C256 的读写程序 －－－－－－ */
bit   RW24xx(unsigned char *DataBuff,unsigned char Length,unsigned int Addr,
                     unsigned char Control,enum eepromtype enumer)
{ void Delay(unsigned char DelayCount);  /*   延时   */
  void Start(void);  /*   启动总线   */
  void Stop(void);   /*   停止IIC总线   */
  bit  RecAck(void); /*   检查应答位   */
  void NoAck(void);  /*   不对IIC总线产生应答   */
  void Ack(void);    /*   对IIC总线产生应答   */
  unsigned char Receive(void); /*   从IIC总线上读数据子程序  */
  void Send(unsigned char sendbyte); /*   向IIC总线写数据   */
  unsigned char data j,i=ERROR;
  bit errorflag=1;  /*   出错标志   */
  while(i--)
  { Start();  /*   启动总线   */
    Send(Control & 0xfe); /*   向IIC总线写数据，器件地址 */
    if(RecAck()) continue; /*   如写不正确结束本次循环   */
    if(enumer > AT2416)
    { Send((unsigned char)(Addr >> 8));//把整型数据转换为字符型数据：弃高取低，只取低8位.如果容量大于32K位，使用16位地址寻址，写入高八位地址
      if(RecAck())  continue;
    }
    Send((unsigned char)Addr); /*   向IIC总线写数据   */
    if(RecAck())  continue; /*   如写正确结束本次循环   */
    if(!(Control & 0x01))   //判断是读器件还是写器件
    { j=Length;
      errorflag=0;         /* 清错误特征位 */
      while(j--)
      { Send(*DataBuff++); /*   向IIC总线写数据   */
        if(!RecAck()) continue; /*   如写正确结束本次循环   */
        errorflag=1;
        break;
      }
      if(errorflag==1) continue;
      break;
    }
    else
    { Start();  /*   启动总线   */
      Send(Control); /*   向IIC总线写数据   */
      if(RecAck()) continue;//器件没应答结束本次本层循环
      while(--Length)  /*   字节长为0结束   */
      { *DataBuff ++= Receive();
        Ack();   /*   对IIC总线产生应答   */
      }
      *DataBuff=Receive(); /* 读最后一个字节 */
      NoAck();  /*   不对IIC总线产生应答   */
      errorflag=0;
      break;
    }
  }
  Stop();  /*   停止IIC总线   */
  if(!(Control & 0x01))
  { Delay(255); Delay(255); Delay(255); Delay(255);
  }
  return(errorflag);
}

/* * * * * 以下是对IIC总线的操作子程序 * * * * */
/* * * * * * 启动总线 * * * * */
void Start(void)
{ SCL=0; /* SCL处于高电平时,SDA从高电平转向低电平表示 */
  SDA=1; /* 一个"开始"状态,该状态必须在其他命令之前执行 */
  SCL=1;
  _nop_(); _nop_(); _nop_();
  SDA=0;
  _nop_(); _nop_(); _nop_(); _nop_();
  SCL=0;
  SDA=1;    
}

/* * * * * 停止IIC总线 * * * * */
void Stop(void)
{ SCL=0; /*SCL处于高电平时,SDA从低电平转向高电平 */
  SDA=0; /*表示一个"停止"状态,该状态终止所有通讯 */
  SCL=1;
  _nop_(); _nop_(); _nop_(); /* 空操作 */
  SDA=1;
  _nop_(); _nop_(); _nop_();
  SCL=0;
}

/* * * * * 检查应答位 * * * * */
bit RecAck(void)
{ SCL=0;
  SDA=1;
  SCL=1;
  _nop_(); _nop_(); _nop_(); _nop_();
  CY=SDA;     /* 因为返回值总是放在CY中的 */
  SCL=0;
  return(CY);
}

/* * * * *对IIC总线产生应答 * * * * */
void Ack(void)
{ SDA=0; /* EEPROM通过在收到每个地址或数据之后, */
  SCL=1; /* 置SDA低电平的方式确认表示收到读SDA口状态 */
  _nop_(); _nop_(); _nop_(); _nop_();
  SCL=0;
  _nop_();
  SDA=1;
}

/* * * * * * * * * 不对IIC总线产生应答 * * * * */
void NoAck(void)
{ SDA=1;
  SCL=1;
  _nop_(); _nop_(); _nop_(); _nop_();
  SCL=0;
}

/* * * * * * * * * 向IIC总线写数据 * * * * */
void Send(unsigned char sendbyte)
{ unsigned char data j=8;
  for(;j>0;j--)
  { SCL=0;
    sendbyte <<= 1; /* 使CY=sendbyte^7; */
    SDA=CY; /* CY 进位标志位 */
    SCL=1;
  }
  SCL=0;
}

/* * * * * * * * * 从IIC总线上读数据子程序 * * * * */
unsigned char Receive(void)
{ register receivebyte,i=8;
  SCL=0;
  while(i--)
  { SCL=1;
    receivebyte = (receivebyte <<1 ) | SDA;
    SCL=0;
  }
  return(receivebyte);
}

/* * * * * * * * 一个简单延时程序 * * * * * * * * * * * * */
void Delay(unsigned char DelayCount)
{ while(DelayCount--);
}

/* －－－－－  AT24C01～AT24C256 的读写程序 －－－－－－ */
void main()
{ unsigned char Control,*p1,*p2;
  unsigned char Length;
  unsigned int addr ; /* 24Cxx片内地址 */
  p1=buf1;p2=buf2;
  addr=0; /* 片内地址 AT24C256为0～32767 */
  Length=8; /* 读写长度 */
  enumer=AT24256; /* 读写AT24C256 */
  Control=0xa0; /* 写操作 */
  RW24xx(p1,Length,addr,Control,enumer); /* 写 */
  Control=0xa1; /* 读操作 */
  RW24xx(p2,Length,addr,Control,enumer); /* 读 */
}
