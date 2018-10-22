#include<stdio.h>

typedef enum Q1{Q1Send, Q1Recv} Q1;
typedef enum Q2{Q2None, Q2Send, Q2Recv} Q2;

void f2(){
     printf("C");
}

void g2(){
     printf("D");
}

//Inconsistency between case labels
void f_EMU_2(Q1 q){
     switch (q){
          case Q1Send: f2(); break;
          case Q2Recv: g2(); break;
     }
}
