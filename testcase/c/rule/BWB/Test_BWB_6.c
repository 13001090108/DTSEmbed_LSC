int f (int x, int y, int z)
{
    if(x>0){
      x=x+1;
    }else if(x<0){
      x=x-2;
    }else{
      if(y>0){
        x=y+2;
      }else
        x=y-3;
      if(z>x){
        x++;
      }        
    }
    return x;
}
