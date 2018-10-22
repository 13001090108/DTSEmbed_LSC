void g(int x,int y){
int b[8];
b[y+x] = 3;

}
int main(){

	int i = 9;
	g(5,i-2);//OOBPRE
	g(5,12);//OOBPRE 

}
