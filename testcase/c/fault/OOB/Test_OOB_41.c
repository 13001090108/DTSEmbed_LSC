char *ghx_oob_1_f1()
{
    char mm[200];
	int cc;
	char ff;

	for (cc=0; cc<=200; cc++)
	{
		ff=mm[cc]; //DEFECT,OOB,mm
	}

	return 0;
}
