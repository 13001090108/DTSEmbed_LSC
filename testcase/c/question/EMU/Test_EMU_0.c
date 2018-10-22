#include<stdio.h>
typedef enum Q1{Q1Send, Q1Recv} Q1;
typedef enum Q2{Q2None, Q2Send, Q2Recv} Q2;
void f(){
     printf("A");
}
void g(){
     printf("B");
}
void f_EMU_1(Q1 q){
     switch (q){
          case Q2Send: f(); break;
          case Q2Recv: g(); break;
     }
}
