void foo() {
    int x = 3; 
    while(x>0)
   x++;
    do {
      	x++;
    } while (x = 10);// defect - the condition is constant
    do {
      	x--;
    } while (0);// Ok - typical usage of 'do' construct when a user wants to //organize a code block     
    do {
     	return;
    } while (true);// Ok - typical usage of 'do' construct when a user wants to //organize a infinite loop     
	do
    {
       x =x+3;
    }while(x>0);
    do
    {
 		x=x+5;
    }while(3+2+1);//defect
    do
	{
      x=x-2;
	}while(sizeof(int)+x<5);

}
