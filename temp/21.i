# 1 "E:\\TESTCASE\\\345\215\225\345\205\203\345\206\205\\2.c"
# 1 "<built-in>"
# 1 "<command line>"





# 1 "E:/lib/Workspace/DTSEmbed_LSC\\cpp\\defines.txt" 1
# 35 "E:/lib/Workspace/DTSEmbed_LSC\\cpp\\defines.txt"
 typedef char * va_list;
# 7 "<command line>" 2
# 1 "E:\\TESTCASE\\\345\215\225\345\205\203\345\206\205\\2.c"
void f1(){
 int a;
 scanf("%d", &a);
 int b = 1;
 int m = a + b + 10;
 int n = 100;
 f2(m , n);
}
void f2(int m , int n){
 int x = 1;
 int y = n + x + 10;
 int h = m + 10;
 f3(m);
}

void f3(int n){
 int b = 10;
 int a;
 a = n + 1;
 f4(a);
}

void f4(int m){
 int x = 1;
 int y = 10;
 if(x > 10) {
  x ++;
  y ++;
 }
 else {
  x = 10;
 }
 int a = m+10;
 int b = m+1 ;
 f6(b , a);
}
# 50 "E:\\TESTCASE\\\345\215\225\345\205\203\345\206\205\\2.c"
int f6(int a , int b) {
 int m = a + 10;
 int n = a - 10;
 if(m > 1) {
  m = 10;
 }
 else {
  m ++;
 }
 int c = m + n;
 return c;
}
