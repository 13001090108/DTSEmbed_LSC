void f_PF(int a , int b) {}
void f_PF_1() {
     void (*proc_pointer)(int a, int b) = f_PF;//PF
     proc_pointer(1,2);
}
