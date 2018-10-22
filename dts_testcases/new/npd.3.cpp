class B
{
  public:  void fun(){int a = 1;}
};
class A
{
   B *p;
  void test()
  {
    if(p==NULL)
    {   int i = 0;}
    p->fun();
   }    
};




