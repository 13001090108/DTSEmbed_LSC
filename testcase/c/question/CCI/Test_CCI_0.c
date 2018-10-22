
void foo() {
	int i=0,x=0,y=1;
   if (sizeof(char) < 2)  // defect - the condition is constant
   {
    i =i+1;  	
   }
   if(sizeof(char) ==1) //defect
    i++;
   if(sizeof(int)+1+4 +x < y )
	x++;
   if(3+2-34 >1) //defect
   {
     i= i-1;
   }
  if(x>3)
	i++;
  if(x=2) //defect
   y++;
}
