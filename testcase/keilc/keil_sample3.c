/*==============================================================
1ms时标 混合式调度器（一个抢占式任务，多个合作式任务）
作者：shadow.hu
===============================================================*/
#include<reg52.h>
#define uchar  unsigned char
#define ushort unsigned short
#define SCH_MAX_TASKS 9
#define ERROR_SCH_TOO_MANY_TASKS  9
#define ERROR_SCH_CANOT_DELETE_TASK 0
#define RETURN_ERROR 0
#define RETURN_NORMAL 1

#define INTERRPT_Timer_2_Overflow 5

#define SCH_REPORT_ERRORS
#ifdef  SCH_REPORT_ERRORS
#define Error_Port P1
#endif

typedef data struct
{
    void (code *pTask)(void);
 ushort Delay;
 ushort Period;
 ushort RunMe;
 uchar  Co_op;//如果任务是合作式的，设置为1，如果任务是抢占式的，设置为0
}sTask;
sTask SCH_tasks_G[SCH_MAX_TASKS];

void SCH_Init_T2(void);
uchar SCH_Add_Task(void (code * pFunction)(),const ushort Delay,   ushort PERIOD,	bit Co_op);
//                      函数名指针                 延时的时标数    执行任务的时间间隔
//                                                 为0则立即执行   如果为0，表示单次任务  
void SCH_Dispatch_Tasks(void);
void SCH_Start(void);
bit SCH_Delete_Task(const ushort TASK_INDEX);
void SCH_Go_To_Sleep(void);
void SCH_Report_Status(void);//报告系统状况
void LED_Flash_Init(void);
void LED_Flash_Update_A(void);
void LED_Flash_Update_B(void);
void LED_Flash_Update_C(void);
void LED_Flash_Update_D(void);
void LED_Flash_Update_E(void);
void LED_Flash_Update_F(void);
void LED_Flash_Update_G(void);
void LED_Flash_Update_H(void);

uchar Error_code_G = 0;//
static ushort Error_tick_count_G;//记住自从上一次纪录错误以来的时间
static uchar Last_error_code_G;//上次的错误代码（在1分钟之后复位）

uchar  LED_State_G_A = 0;
uchar  LED_State_G_B = 0;
uchar  LED_State_G_C = 0;
uchar  LED_State_G_D = 0;
uchar  LED_State_G_E = 0;
uchar  LED_State_G_F = 0;
uchar  LED_State_G_G = 0;
uchar  LED_State_G_H = 0;

sbit LED_pin_A = P1^0;
sbit LED_pin_B = P1^1;
sbit LED_pin_C = P1^2;
sbit LED_pin_D = P1^3;
sbit LED_pin_E = P1^4;
sbit LED_pin_F = P1^5;
sbit LED_pin_G = P1^6;
sbit LED_pin_H = P1^7;

//Error_code_G = ERROR_SCH_TOO_MANY_TASKS;
//Error_code_G = ERROR_SCH_WAITING_FOR_SLAVE_TO_ACK;
//Error_code_G = ERROR_SCH_WAITING_FOR_START_COMAND_FROM_MASTER;
//Error_code_G = ERROR_SCH_ONE_OR_MORE_SLAVES_DID_NOT_START;
//Error_code_G = ERROR_SCH_LOST_SLAVE;
//Error_code_G = ERROR_SCH_CAN_BUS_ERROR;
//Error_code_G = ERROR_I2C_WRITE_BYTE_AT24C64;

void main(void)
{
 SCH_Init_T2();
 LED_Flash_Init();
 SCH_Add_Task(LED_Flash_Update_A,0,1000);//添加一个任务
 SCH_Add_Task(LED_Flash_Update_B,0,2000);//添加一个任务
 SCH_Add_Task(LED_Flash_Update_C,0,3000);//添加一个任务
 SCH_Add_Task(LED_Flash_Update_D,0,4000);//添加一个任务
 SCH_Add_Task(LED_Flash_Update_E,0,5000);//添加一个任务
 SCH_Add_Task(LED_Flash_Update_F,0,6000);//添加一个任务
 SCH_Add_Task(LED_Flash_Update_G,0,7000);//添加一个任务
 SCH_Add_Task(LED_Flash_Update_H,0,8000);//添加一个任务

 SCH_Start();//开全局中断
 while(1)
 {
  SCH_Dispatch_Tasks();
 }
}
void calc (i,b) 
char i;
int b;

{
  
}

/*------------------------------------------------------------
 这是调度器的中断服务程序，初始化函数中的定时器设置决定了它
的调度频率，这个版本的调度器由定时器2触发中断，定时器自动重装。
-------------------------------------------------------------*/
void SCH_Update(void) interrupt INTERRPT_Timer_2_Overflow
{
 //刷新任务队列
 uchar Index;
 TF2 = 0;//必须手工清除
 //注意：计算单位为"时标"（不是毫秒）
 for(Index = 0;Index < SCH_MAX_TASKS;Index++)
 {   //检测这里是否有任务
  if(SCH_tasks_G[Index].pTask)
  { 
   if(SCH_tasks_G[Index].Delay == 0)
   {
    //任务需要运行，间隔的时间已经到了
    if(SCH_tasks_G[Index].Co_op)
    {
     //如果是合作式任务，RunMe标志加1
     SCH_tasks_G[Index].RunMe += 1;//要执行任务的标志加1
    }
    else//如果它是抢占式任务，立即运行它
    {
     (*SCH_tasks_G[Index].pTask)();//运行任务
     SCH_tasks_G[Index].RunMe -= 1;
     //周期性的任务将自动再次运行，单次任务就删除
     if(SCH_tasks_G[Index].Period == 0)
     {
      SCH_tasks_G[Index].pTask = 0;
     }
    }   
    if(SCH_tasks_G[Index].Period)//时标间隔不等于0
    {
     //调度周期性的任务再次运行，每隔这个固定的时标长度执行一次任务
     SCH_tasks_G[Index].Delay = SCH_tasks_G[Index].Period;
    }
   }
   else //任务有延迟执行要求，还没到达延迟的时间
   {
    //还没有准备好运行,延迟减1
    SCH_tasks_G[Index].Delay -= 1;
   }
  }
 }
}

void SCH_Init_T2(void)
{
    uchar i;
 for(i=0;i<SCH_MAX_TASKS;i++)
 {
  SCH_Delete_Task(i);
 }
 Error_code_G = 0;
 T2CON = 0x04;
 TMOD = 0x00;
 TH2   = 0xfc;
 RCAP2H = 0xfc;
 TL2   = 0x18;
 RCAP2L = 0x18;
 ET2   = 1;
 TR2   = 1;
}
/*----------------------------------------------------------------------------
任务函数每隔一定时间间隔或在用户定义的延迟之后运行
pFunction -- 将被调用的函数名称。注意：被调函数必须是“void void”型
DELAY     -- 在任务第一次被执行之前的间隔
PERIOD    -- 如果它为0，则只调用该函数一次，由DELAY确定其调用的时间
             如果非0，那么它就是被重复调用的时间间隔
Co_op     -- 如果是合作式任务则设置为1，如果是抢占式任务则设置为0.

注意：如果以后要删除任务，将需要返回值
例子：
Task_ID = SCH_Add_Task(Do_X,1000,0,0);
使函数Do_X()在1000个调度器时标之后运行一次（抢占式任务）
Task_ID = SCH_Add_Task(Do_X,0,1000,1);
使函数Do_X()每隔1000个调度器时标运行一次（合作式任务）
Task_ID = SCH_Add_Task(Do_X,300,1000,0);
使函数Do_X()每隔1000个调度器时标运行一次，任务首先在T=300个时标时被执行
   然后是1300个时标.........（抢占式任务）

-----------------------------------------------------------------------------*/
uchar SCH_Add_Task(void (code * pFunction)(),const ushort DELAY, ushort PERIOD,bit Co_op)
{
 uchar Index = 0;
 //首先在队列中找到一个空隙（如果有的话，否则就不添加新任务）
 while((SCH_tasks_G[Index].pTask != 0)&&(Index < SCH_MAX_TASKS))
 {
  Index++;//当一个新任务被添加，且没有超过任务上限
 }
 //是否达到任务队列的结尾？
 if(Index == SCH_MAX_TASKS)//任务数量达到上限
 {
  Error_code_G = ERROR_SCH_TOO_MANY_TASKS;
  return SCH_MAX_TASKS;//直接返回，不添加这个新任务
 }
 //如果能运行到这里，说明任务队列中有空隙，添加任务。
 SCH_tasks_G[Index].pTask = pFunction;
 SCH_tasks_G[Index].Delay = DELAY;
 SCH_tasks_G[Index].Period = PERIOD;
 SCH_tasks_G[Index].Co_op = Co_op;
 SCH_tasks_G[Index].RunMe  = 0;
 return Index;//返回任务的位置（以便以后删除）
}

void SCH_Dispatch_Tasks(void)
{
 uchar Index;
 //调度（运行）下一个任务（如果有任务就绪）
 for(Index = 0;Index < SCH_MAX_TASKS;Index++)
 {
  //只调度合作式任务
  if((SCH_tasks_G[Index].RunMe > 0)&&(SCH_tasks_G[Index].Co_op))
  {
   (*SCH_tasks_G[Index].pTask)();//执行任务
   SCH_tasks_G[Index].RunMe -= 1;//清除任务需要执行的标志
  }
  //如果这是个“单次”任务，将它从队列中删除
  if(SCH_tasks_G[Index].Period == 0)
  {
   SCH_tasks_G[Index].pTask = 0;// 比通过调用来删除任务更快SCH_Delete_Task(Index);
  }
 }
 SCH_Report_Status();//报告系统状况
 SCH_Go_To_Sleep();
}

void SCH_Start(void)
{
 EA = 1;
}

bit SCH_Delete_Task(const ushort TASK_INDEX)
{
 bit Return_code;
 if(SCH_tasks_G[TASK_INDEX].pTask == 0)
 {
  //这里没有任务。。。设置全局错误变量
  Error_code_G = ERROR_SCH_CANOT_DELETE_TASK;
  Return_code = RETURN_ERROR;//返回错误代码
 }
 else
 {
  Return_code = RETURN_NORMAL;
 }
 //删除任务
 SCH_tasks_G[TASK_INDEX].pTask = 0x0000;
 SCH_tasks_G[TASK_INDEX].Delay = 0;
 SCH_tasks_G[TASK_INDEX].Period = 0;
 SCH_tasks_G[TASK_INDEX].RunMe = 0;
 return Return_code;
}

void SCH_Go_To_Sleep()
{
 PCON |= 0x01;//进入休眠模式
}

void SCH_Report_Status(void)
{
/* #ifdef SCH_REPORT_ERRORS
 if(Error_code_G != Last_error_code_G)
 {
  Error_Port = 255 - Error_code_G;
  Last_error_code_G = Error_code_G;
  if(Error_code_G != 0)
  {
   Error_tick_count_G = 60000;
  }
  else
  {
   Error_tick_count_G = 0;
  }
 }
 else
 {
  if(Error_tick_count_G != 0)
  {
   if(--Error_count_G == 0)
   {
    Error_code_G = 0;
   }
  }
 }
 #endif    */
}

void LED_Flash_Update_A(void)
{
 if(LED_State_G_A == 1)
 {
  LED_State_G_A = 0;
  LED_pin_A = 0;
 }
 else
 {
  LED_State_G_A = 1;
  LED_pin_A = 1;
 }
}

void LED_Flash_Update_B(void)
{
 if(LED_State_G_B == 1)
 {
  LED_State_G_B = 0;
  LED_pin_B = 0;
 }
 else
 {
  LED_State_G_B = 1;
  LED_pin_B = 1;
 }
}

void LED_Flash_Update_C(void)
{
 if(LED_State_G_C == 1)
 {
  LED_State_G_C = 0;
  LED_pin_C = 0;
 }
 else
 {
  LED_State_G_C = 1;
  LED_pin_C = 1;
 }
}
void LED_Flash_Update_D(void)
{
 if(LED_State_G_D == 1)
 {
  LED_State_G_D = 0;
  LED_pin_D = 0;
 }
 else
 {
  LED_State_G_D = 1;
  LED_pin_D = 1;
 }
}
void LED_Flash_Update_E(void)
{
 if(LED_State_G_E == 1)
 {
  LED_State_G_E = 0;
  LED_pin_E = 0;
 }
 else
 {
  LED_State_G_E = 1;
  LED_pin_E = 1;
 }
}
void LED_Flash_Update_F(void)
{
 if(LED_State_G_F == 1)
 {
  LED_State_G_F = 0;
  LED_pin_F = 0;
 }
 else
 {
  LED_State_G_F = 1;
  LED_pin_F = 1;
 }
}
void LED_Flash_Update_G(void)
{
 if(LED_State_G_G == 1)
 {
  LED_State_G_G = 0;
  LED_pin_G = 0;
 }
 else
 {
  LED_State_G_G = 1;
  LED_pin_G = 1;
 }
}
void LED_Flash_Update_H(void)
{
 if(LED_State_G_H == 1)
 {
  LED_State_G_H = 0;
  LED_pin_H = 0;
 }
 else
 {
  LED_State_G_H = 1;
  LED_pin_H = 1;
 }
}

void LED_Flash_Init(void)
{
 LED_State_G_A= 0;//初始化LED状态
 LED_State_G_B= 0;//初始化LED状态
 LED_State_G_C= 0;//初始化LED状态
}