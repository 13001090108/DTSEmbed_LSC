#include<grp.h>
#include<sys/types.h>
main()
{
struct group *data;
int i;
while((data= getgrent())!=0){
i=0;
printf("%s:%s:%d:",data->gr_name,data->gr_passwd,data->gr_gid);
while(data->gr_mem[i])printf("%s,",data->gr_mem[i++]);
printf("\n");
}
}
