int foo_5_6() {
return 0;
}
int ff_5_6(int i) {
if (foo_5_6() && i) {
    // do something
}
10 % foo_5_6();
return 0;
}
