int calc (char i, int b) reentrant  {
  int  x;
  x = table [i];
  return (x * b);
}

unsigned int  interruptcnt;
unsigned char second;

void timer0 (void) interrupt 1 using 2  {
  if (++interruptcnt == 4000)  {    /* count to 4000 */
    second++;                       /* second counter    */
    interruptcnt = 0;               /* clear int counter */
  }
}


extern bit alarm;
int alarm_count;
   
void falarm (void) interrupt 1 using 3  {
  alarm_count *= 2;
  alarm = 1;
}