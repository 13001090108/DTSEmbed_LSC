void foo() {
    	int x = 3;
    	do {
      		x++;
    	} while (x = 10);  // defect - the condition is constant
    	do {
      		x--;
    	} while (0);       
     // Ok - typical usage of 'do' construct when a user wants to  //organize a code block     
    	do {
     	 	return;
    } while (true);    
// Ok - typical usage of 'do' construct when a user wants to //organize a infinite loop     
   }
