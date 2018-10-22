void foo() {
  int x = 3;
  while (x = 3)   // defect - the condition is constant
  {
      	x++;
  } 
// Ok - typical usage of 'do' construct when a user wants to //organize a infinite loop     
  while (true)    
  {
      	/* ... */
  }
 }
