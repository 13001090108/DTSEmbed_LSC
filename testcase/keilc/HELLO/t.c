struct link
  {
  struct link idata *next;
  char code *test;
  };

struct link idata list  _at_ 0x40;     /* list at idata 0x40 */
xdata char  text[256]   _at_ 0xE000;   /* array at xdata 0xE000 */
xdata i1           _at_ 0x8000;   /* int at xdata 0x8000 */
volatile char xdata IO _at_ 0xFFE8;   /* xdata I/O port at 0xFFE8 */
char far ftext[256]    _at_ 0x02E000; /* array at xdata 0x03E000 */
xdata char bb _at_ 0x0000;
void main ( void ){
  list.next = (void *) 0;
  i1        = 0x1234;
  text [0]  = 'a';
  IO        = 6;
  ftext [0] = 'f';
}
  fun();
