int func2()
{
    char *s = getenv("ConFig_File");
    if (strcmp(s, "C:\\read.ini") == 0) {
        fopen(s, "r");
    }
    return 0;
}
