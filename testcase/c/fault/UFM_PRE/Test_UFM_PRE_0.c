  #include <stdlib.h>
  typedef struct x {
      char * field;
  } tx;
  
  void release(tx * a){
      a->field = "ab";
 }
 
 int main() {
     tx *a = (tx *)malloc(sizeof(tx));
     if (a==0) return;
     a->field = (char *)malloc(10);
     free(a);
     release(a);
    
}
