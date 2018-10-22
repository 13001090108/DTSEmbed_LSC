int jhb_iao_2_f1(int t){
		int x=10;
		return (x/t);
		
	}
void jhb_iao_2_f2(){
		int i;
		i=jhb_iao_2_f1(0);   //DEFECT
}
