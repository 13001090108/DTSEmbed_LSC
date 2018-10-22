char data var1;
char code text[] = "ENTER PARAMETER:";
unsigned long xdata array[100];
float idata x,y,z;
unsigned int pdata dimension;
unsigned char xdata vector[10][4][4];
char bdata flags;

data char x;   // Old-Style Memory Type Declaration
char data x;   // New-Style Memory Type Declaration

data char *x;   // Old-Style Memory Type Declaration
char *data x;   // New-Style Memory Type Declaration

static bit done_flag = 0;    /* bit variable */

bit testfunc (               /* bit function */
  bit flag1,                 /* bit arguments */
  bit flag2)
{
return (0);                  /* bit return value */
}

int bdata ibase;        /* Bit-addressable int */

char bdata bary [4];    /* Bit-addressable array */

sbit mybit0 = ibase ^ 0;      /* bit 0 of ibase */
sbit mybit15 = ibase ^ 15;    /* bit 15 of ibase */

sbit Ary07 = bary[0] ^ 7;     /* bit 7 of bary[0] */
sbit Ary37 = bary[3] ^ 7;     /* bit 7 of bary[3] */

extern bit mybit0;      /* bit 0 of ibase */
extern bit mybit15;     /* bit 15 of ibase */

extern bit Ary07;       /* bit 7 of bary[0] */
extern bit Ary37;       /* bit 7 of bary[3] */

Ary37 = 0;        /* clear bit 7 in bary[3] */
bary[3] = 'a';    /* Byte addressing */
ibase = -1;       /* Word addressing */
mybit15 = 1;      /* set bit 15 in ibase */

union lft
  {
  float mf;
  long ml;
  };

bdata struct bad
  {
  char m1;
  union lft u;
  } tcp;

sbit tcpf31 = tcp.u.ml ^ 31;        /* bit 31 of float */
sbit tcpm10 = tcp.m1 ^ 0;
sbit tcpm17 = tcp.m1 ^ 7;

char *s;       /* string ptr */
int *numptr;   /* int ptr */
long *state;   /* Texas */


           char *c_ptr;          /* char ptr */
           int  *i_ptr;          /* int ptr */
           long *l_ptr;          /* long ptr */
   
           void main (void)
           {
          char data dj;         /* data vars */
          int  data dk;
          long data dl;
     
         char xdata xj;        /* xdata vars */
         int  xdata xk;
         long xdata xl;
     
         char code cj = 9;     /* code vars */
         int  code ck = 357;
         long code cl = 123456789;
     
     
         c_ptr = &dj;          /* data ptrs */
         i_ptr = &dk;
         l_ptr = &dl;
     
         c_ptr = &xj;          /* xdata ptrs */
         i_ptr = &xk;
         l_ptr = &xl;
     
         c_ptr = &cj;          /* code ptrs */
         i_ptr = &ck;
         l_ptr = &cl;
         }

char * xdata strptr;     /* generic ptr stored in xdata */
int * data numptr;       /* generic ptr stored in data */
long * idata varptr;     /* generic ptr stored in idata */

char data *str;        /* ptr to string in data */
int xdata *numtab;     /* ptr to int(s) in xdata */
long code *powtab;     /* ptr to long(s) in code */

char data * xdata str;         /* ptr in xdata to data char */
int xdata * data numtab;       /* ptr in data to xdata int */
long code * idata powtab;      /* ptr in idata to code long */

           char data  *c_ptr;      /* memory-specific char ptr */
           int  xdata *i_ptr;      /* memory-specific int ptr */
           long code  *l_ptr;      /* memory-specific long ptr */
   
           long code powers_of_ten [] =
             {
             1L,
             10L,
             100L,
            1000L,
            10000L,
            100000L,
            1000000L,
            10000000L,
            100000000L
            };
  
          void main (void)
          {
         char data strbuf [10];
         int xdata ringbuf [1000];
     
         c_ptr = &strbuf [0];
         i_ptr = &ringbuf [0];
         l_ptr = &powers_of_ten [0];
         }

unsigned char xdata foo;
unsigned char xdata *foo_ptr = &foo;

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

