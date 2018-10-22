void yxh_oob_f1()
{
	char buf[3];
	
	*(buf+4) = 'c'; //DEFECT
	char c = *(buf+4); //DEFECT
	
	char *q = buf+4; //DEFECT
	char *p = (buf+4); //DEFECT
	char *r;
	r = buf+4; //DEFECT
	r = (buf+4); //DEFECT
}
