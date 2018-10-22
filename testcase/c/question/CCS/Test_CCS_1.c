void fun0()
{
	int i=1;
    switch(sizeof(char) ==9 )//defect
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
