void foo() {
  if (sizeof(char) < 2)  // defect - the condition is constant
   {
      	/* ... */
   }
 }
