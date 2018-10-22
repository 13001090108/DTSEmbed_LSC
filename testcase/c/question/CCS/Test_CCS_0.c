void fun0()
{
	int i=1;
    switch(1+2)//defect
	{
		case 0:
            i++;
            break;
        case 1:
            i--;
            break;
        default:
            break;
	}
}
