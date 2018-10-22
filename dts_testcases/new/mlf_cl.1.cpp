class A
{
    int *f;
  void test()
{
   f = new int(1);
}
~A()
{
  delete f;
}
};
