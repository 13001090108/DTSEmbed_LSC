#define NULL 0

int f_RS_2(int c)
{
    int i = 5;
    if(c){
        return i;
    }else{
        return --i;
    }
    return i;//RS,defect
}
