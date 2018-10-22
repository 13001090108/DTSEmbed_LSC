void doA(void);
void doB(void); 
void doC(void); 

void func() {
  int a = 1;
  if(a > 0)
    doA();
  if(a==0)
    doB();
  else
    doC(); 
}
