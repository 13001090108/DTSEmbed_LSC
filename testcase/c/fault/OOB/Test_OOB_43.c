int k;
f1(int i){
char buf[10];
k=10;i=k;buf[i]=1;//参数局部化
}

f2(){
k=9;
f1(k);
}
