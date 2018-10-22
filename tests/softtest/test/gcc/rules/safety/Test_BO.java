package softtest.test.gcc.rules.safety;

import java.util.Arrays;
import java.util.Collection;
import java.util.Set;

import org.junit.BeforeClass;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.interpro.c.InterContext;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class Test_BO extends ModelTestBase{
	public Test_BO(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/safety/BO-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/bo_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] 
				 {
	/////////////////  0   ///////////////////	
	                {   //约束缺失测试用例  
//通过调用strcpy()，将字符串“AAA…AAA“复制到buf中，但是由于字符串的长度超过了buf的容量，
	                	//所以将导致缓冲区溢出。可能发生相同类型错误的函数还包括strncpy。
	                    "#include<string.h>"                                                   +"\n"+
	                    "int main(int argc,char*argv[]){"                                      +"\n"+
	                    "char buf[10];"                                                        +"\n"+
	                    "strcpy(buf,\"AAAAAAAAAAAAAA\");"                                        +"\n"+
	                    "return 0;"                                                            +"\n"+
	                    "}"                                                                    
	                    ,
	                    "gcc"
	                    ,
	                    "BO"
	                    ,
	                    },


//////////////////////////1//////////////////////////////////////////////
	                    {
				            "#include <string.h>"                                                  +"\n"+
				            ""                                                                     +"\n"+
				            "void f1()"                                                            +"\n"+
				            "{"                                                                    +"\n"+
				            "	char buffer2[15]=\"1234567890\",buffer1[10];"                          +"\n"+
				            "	strcpy (buffer1,buffer2);//DEFECT"                                   +"\n"+
				            "	"                                                                    +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "BO"
				            ,
				            },
//////////////////////////2//////////////////////////////////////////////	
				            {//C/C++有些输入函数，在从外界读取内容的时候，没有限定读入数据的长度。当读入的数据长度超过分配的内存限制，
		                    	//将会导致系统内存数据被破坏、程序崩溃或者执行恶意代码等问题。
		                    	//这个例子是描述fgets()函数的类似的还有read ，fread,LoadString
		    		            "	#include<stdio.h>"                                                   +"\n"+
		    		            "    #include <stdlib.h>"                                              +"\n"+
		    		            "	#include <string.h>"                                                 +"\n"+
		    		            "	#define bufsize 256"                                                 +"\n"+
		    		            "	int main () {"                                                       +"\n"+
		    		            "	      char input[bufsize];"                                          +"\n"+
		    		            "		  char dest[20];"                                                   +"\n"+
		    		            "		  printf(\"Enter file name:\\n\");"                                    +"\n"+
		    		            "		  scanf(\"%s\",input);"                                               +"\n"+
		    		            "		  FILE *fp;"                                                        +"\n"+
		    		            "		  if((fp=fopen(input,\"r\"))==NULL)"                                  +"\n"+
		    		            "		  {"                                                                +"\n"+
		    		            "	          printf(\"Cannot open file!\\n\");"                            +"\n"+
		    		            "          getchar();"                                                 +"\n"+
		    		            "	          exit(1);"                                                  +"\n"+
		    		            "	      }"                                                             +"\n"+
		    		            "		  fgets(dest,bufsize,fp);"                                          +"\n"+
		    		            "		  printf(\"%s\",dest);"                                               +"\n"+
		    		            "		 "                                                                  +"\n"+
		    		            "		  return 0;"                                                        +"\n"+
		    		            "	}"                                                                   
		    		            ,
		    		            "gcc"
		    		            ,
		    		            "BO"
		    		            ,
		    		            },

//////////////////////////3//////////////////////////////////////////////
		    		            {//C/C++中有些字符串操作函数在制定缓冲区边界时是根据源数据的大小而不是根据目标数据的大小。
		    		            	//这样，当源数据的大小超过目标数据分配的大小时，将会导致缓冲区溢出。
					                "#include<string.h>"                                                   +"\n"+
					                "int main(){"                                                          +"\n"+
					                "char a[10];"                                                          +"\n"+
					                "char b[100];"                                                         +"\n"+
					                "strcpy(a,b);"                                                         +"\n"+
					                "}"                                                                    
					                ,
					                "gcc"
					                ,
					                "BO"
					                ,
					                },

//////////////////////////4//////////////////////////////////////////////
						            {
							            "#include <string.h>"                                                  +"\n"+
							            ""                                                                     +"\n"+
							            "void f1()"                                                            +"\n"+
							            "{"                                                                    +"\n"+
							            "	int a=11;"                                                           +"\n"+
							            "	char buffer2[15]=\"1234567890\",buffer1[10];"                          +"\n"+
							            "	strncat (buffer1,buffer2,11);//DEFECT"                               +"\n"+
							            "	strncat (buffer1,buffer2,a);//DEFECT"                                +"\n"+
							            "}"                                                                    
							            ,
							            "gcc"
							            ,
							            "BO"
							            ,
							            },


/////////////////////////5//////////////////////////////////////////////
						                {//strncat函数
								            "#include <string.h>"                                                  +"\n"+
								            ""                                                                     +"\n"+
								            "void f1()"                                                            +"\n"+
								            "{"                                                                    +"\n"+
								            "	int a=11;"                                                           +"\n"+
								            "	char buffer2[15]=\"1234567890\",buffer1[10];"                          +"\n"+
								            "	strncat (buffer1,buffer2,11);//DEFECT"                               +"\n"+
								            "	strncat (buffer1,buffer2,a);//DEFECT"                                +"\n"+
								            "}"                                                                    
								            ,
								            "gcc"
								            ,
								            "BO"
								            ,
								            },
//////////////////////////6///////////////////////////////////////////////////
								            {//C++中一部分函数可以直接对内存区域进行操作，当被操作的内存的大小没有被监控时，会发生内存溢出。
								            	//memcpy函数
								                "	int main()"                                                          +"\n"+
								                "	{"                                                                   +"\n"+
								                "	    char a[100];"                                                    +"\n"+
								                "	    char b[50];"                                                     +"\n"+
								                "    memcpy(b,a,sizeof(b));"                                           +"\n"+
								                "}"                                                                    
								                ,
								                "gcc"
								                ,
								                "OK"
								                ,
								                },
//////////////////////////7 //////////////////////////////////////////////
		                                    {
		                			            "#include <stdio.h> "                                                                    +"\n"+

		                		            "void fopen_compchk()"                                                +"\n"+
		                		            "{ "                                                                   +"\n"+
		                		            " char tmpfile[16384];"                                                +"\n"+
		                		            " fopen_comp(tmpfile, 1);"                                             +"\n"+
		                		            "}"                                                                    +"\n"+
		                		            ""                                                                     +"\n"+
		                		            "void fopen_comp(const char *file, int flag)"                         +"\n"+
		                		            "{"                                                                    +"\n"+
		                		            "   "                                                                  +"\n"+
		                		            "   char command[16384];"                                              +"\n"+
		                		            "   if (flag) "                                                        +"\n"+
		                		            "   {"                                                                 +"\n"+
		                		            "       sprintf(command, \"gzip.exe -d -c %s\", file);"                                +"\n"+
		                		            "   }"                                                                 +"\n"+
		                		            "}"                                                                    
		                		            ,
		                		            "gcc"
		                		            ,
		                		            "BO"
		                		            ,
		                		            },
//////////////////////////8//////////////////////////////////////////////
		                		            {
		                			            "#include <stdio.h> "                                                                    +"\n"+

		                		            "void fopen_compchk()"                                                +"\n"+
		                		            "{ "                                                                   +"\n"+
		                		            " char tmpfile[16384];"                                                +"\n"+
		                		            " fopen_comp(tmpfile, 1);"                                             +"\n"+
		                		            "}"                                                                    +"\n"+
		                		            ""                                                                     +"\n"+
		                		            "void fopen_comp(const char *file, int flag)"                         +"\n"+
		                		            "{"                                                                    +"\n"+
		                		            "   "                                                                  +"\n"+
		                		            "   char command[16384];"                                              +"\n"+
		                		            "   if (flag) "                                                        +"\n"+
		                		            "   {"                                                                 +"\n"+
		                		            "       sprintf(command, \"gzip.exe -d -c %s\", file);"                                +"\n"+
		                		            "   }"                                                                 +"\n"+
		                		            "}"                                                                    
		                		            ,
		                		            "gcc"
		                		            ,
		                		            "BO"
		                		            ,
		                		            },
//////////////////////////9//////////////////////////////////////////////
		                		            {
		                					       "#include <string.h> "                                                                    +"\n"+

		                				            "void fopen_compchk(char *file)"                                                +"\n"+
		                				            "{ "                                                                   +"\n"+
		                				            " char tmpfile[16384];"                                                +"\n"+
		                				            "  strcpy(tmpfile, file);"                                             +"\n"+
		                				            "}"                                                                    
		                				            ,
		                				            "gcc"
		                				            ,
		                				            "BO"
		                				            ,
		                				            },
//////////////////////////10//////////////////////////////////////////////	
		                				            {
		                					            ""                                                                     +"\n"+
		                					            "#include <stdio.h>"                                                   +"\n"+
		                					            ""                                                                     +"\n"+
		                					            "void f1()"                                                            +"\n"+
		                					            "{"                                                                    +"\n"+
		                					            "	char buffer1[10];"                                                    +"\n"+
		                					            ""                                                                     +"\n"+
		                					            "	gets(buffer1);//DEFECT"                                              +"\n"+
		                					            ""                                                                     +"\n"+
		                					            "}"                                                                    
		                					            ,
		                					            "gcc"
		                					            ,
		                					            "BO"
		                					            ,
		                					            },
//////////////////////////11//////////////////////////////////////////////
		                					 		   {
		                					                "int main(){"                                                          +"\n"+
		                					                "char a[10];"                                                          +"\n"+
		                					                "char b[100];"                                                         +"\n"+
		                					                "strncpy(a,b,10);"                                                     +"\n"+
		                					                "}"                                                                    
		                					                ,
		                					                "gcc"
		                					                ,
		                					                "BO_PRE"
		                					                ,
		                					                },

		                			 
//////////////////////////12//////////////////////////////////////////////
		                						            {
		                							            ""                                                                     +"\n"+
		                							            "#include <stdio.h>"                                                   +"\n"+
		                							            ""                                                                     +"\n"+
		                							            "void f1()"                                                            +"\n"+
		                							            "{"                                                                    +"\n"+
		                							            "	char buffer2[10],buffer1[10];"                                       +"\n"+
		                							            "	scanf(\"%9s\",buffer1);"                                      +"\n"+
		                							            "}"                                                                    
		                							            ,
		                							            "gcc"
		                							            ,
		                							            "OK"
		                							            ,
		                							            }, 
//////////////////////////13//////////////////////////////////////////////
		                							            {
		                								            ""                                                                     +"\n"+
		                								            "#include <stdio.h>"                                                   +"\n"+
		                								            ""                                                                     +"\n"+
		                								            "void f1()"                                                            +"\n"+
		                								            "{"                                                                    +"\n"+
		                								            "	char buffer1[10]=\"welcome\",buffer2[10]=\"tochina\",buffer3[15];"       +"\n"+
		                								            "	sprintf(buffer3,\"%6s%s\",buffer1,buffer2);"                           +"\n"+
		                								            "}"                                                                    
		                								            ,
		                								            "gcc"
		                								            ,
		                								            "OK"
		                								            ,
		                								            },
//////////////////////////14//////////////////////////////////////////////
		                								            {
		                									            "#include <string.h>"                                                  +"\n"+
		                									            ""                                                                     +"\n"+
		                									            "void f1()"                                                            +"\n"+
		                									            "{"                                                                    +"\n"+
		                									            "	char buffer2[15]=\"1234567890\",buffer1[10];"                          +"\n"+
		                									            "	strcpy (buffer1,buffer2);//DEFECT"                                   +"\n"+
		                									            "	"                                                                    +"\n"+
		                									            "}"                                                                    
		                									            ,
		                									            "gcc"
		                									            ,
		                									            "BO"
		                									            ,
		                									            },
//////////////////////////15移到OOB中//////////////////////////////////////////////
		                									            {
		                										            "#include <string.h>"                                                  +"\n"+
		                										            ""                                                                     +"\n"+
		                										            "void f1()"                                                            +"\n"+
		                										            "{"                                                                    +"\n"+
		                										            "	char buffer1[10];"                                                   +"\n"+
		                										            "	strcpy (buffer1,\"1234567890\");//DEFECT"                              +"\n"+
		                										            "	"                                                                    +"\n"+
		                										            "}"                                                                    
		                										            ,
		                										            "gcc"
		                										            ,
		                										            "BO"
		                										            ,
		                										            },
//////////////////////////16移到OOB中//////////////////////////////////////////////	
		            {
		            "#define BUFSIZE 10"                                                   +"\n"+
		            "#define OFFSET 12"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_20_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *buf;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	buf = new char[BUFSIZE];"                                            +"\n"+
		            "	buf[OFFSET] = 1; //DEFECT"                                           +"\n"+
		            "	buf[0-1] = 2; //DEFECT"                                              +"\n"+
		            ""                                                                     +"\n"+
		            "	*(buf+OFFSET) = 2; //DEFECT"                                         +"\n"+
		            "	*(buf-1) = 3; //DEFECT"                                              +"\n"+
		            "	delete[] buf;"                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
//////////////////////////17//////////////////////////////////////////////	
		            {
			            "#include <string.h>"                                                  +"\n"+
			            ""                                                                     +"\n"+
			            "void f1()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "	int a=11;"                                                           +"\n"+
			            "	char buffer2[15]=\"1234567890\",buffer1[10];"                          +"\n"+
			            "	strncat (buffer1,buffer2,11);//DEFECT"                               +"\n"+
			            "	strncat (buffer1,buffer2,a);//DEFECT"                                +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "BO"
			            ,
			            },
//////////////////////////18/////////////////////////////////////////////	
			            {
				            "#include <string.h>"                                                  +"\n"+
				            ""                                                                     +"\n"+
				            "void f1()"                                                            +"\n"+
				            "{"                                                                    +"\n"+
				            "	char buffer1[10],*p=buffer1;"                                        +"\n"+
				            "	strcpy (p,\"1234567890\");//DEFECT"                                    +"\n"+
				            "	"                                                                    +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "BO"
				            ,
				            },
//////////////////////////19/////////////////////////////////////////////
				            {
					            "#include <string.h>"                                                  +"\n"+
					            ""                                                                     +"\n"+
					            "void f1()"                                                            +"\n"+
					            "{"                                                                    +"\n"+
					            "	char buffer2[15]=\"1234567890\",buffer1[10],*p1=buffer1,*p2=buffer2;"  +"\n"+
					            "	strcpy (buffer1,p2);//DEFECT"                                        +"\n"+
					            "	strcpy (p1,buffer2);//DEFECT"                                        +"\n"+
					            "	"                                                                    +"\n"+
					            "}"                                                                    
					            ,
					            "gcc"
					            ,
					            "BO"
					            ,
					            },

//////////////////////////20//////////////////////////////////////////////
					            {
						            ""                                                                     +"\n"+
						            ""                                                                     +"\n"+
						            "#include <string.h>"                                                  +"\n"+
						            ""                                                                     +"\n"+
						            "void f1()"                                                            +"\n"+
						            "{"                                                                    +"\n"+
						            "	int a=6;"                                                            +"\n"+
						            "	char buffer2[10]=\"WELCOME\",buffer1[5],*p1=buffer1,*p2=buffer2;"      +"\n"+
						            "	strncat(p1,buffer2,6);//DEFECT"                                      +"\n"+
						            "	strncat(p1,buffer2,5);//DEFECT"                                      +"\n"+
						            "	strncat(buffer1,p2,a);//DEFECT"                                      +"\n"+
						            "}"                                                                    
						            ,
						            "gcc"
						            ,
						            "BO"
						            ,
						            },

//////////////////////////21//////////////////////////////////////////////
						            {
							            "#include <string.h>"                                                  +"\n"+
							            ""                                                                     +"\n"+
							            "void f1()"                                                            +"\n"+
							            "{"                                                                    +"\n"+
							            "	char buffer1[10],*p=buffer1;"                                        +"\n"+
							            "	strcpy (p,\"123456789\");//DEFECT"                                    +"\n"+
							            "	"                                                                    +"\n"+
							            "}"                                                                    
							            ,
							            "gcc"
							            ,
							            "OK"
							            ,
							            },
//////////////////////////22//////////////////////////////////////////////
							            {
								            "#include <string.h>"                                                  +"\n"+
								            ""                                                                     +"\n"+
								            "void f1()"                                                            +"\n"+
								            "{	char buffer1[10]=\"123\";"                                                                    +"\n"+
								            "	char *p=buffer1;"                                        +"\n"+
								            "	strcat (p,\"456789\");//DEFECT"                                    +"\n"+
								            "	"                                                                    +"\n"+
								            "}"                                                                    
								            ,
								            "gcc"
								            ,
								            "OK"
								            ,
								            },	
////////////////////////////23////////////////////////////////////////	
								            {
									            "#include <string.h>"                                                  +"\n"+
									            ""                                                                     +"\n"+
									            "int f1(){"                                                            +"\n"+
									            "    int a=3,b;"                                                       +"\n"+
									            "    if(a==3) b=10;"                                                   +"\n"+
									            "    else b=9;"                                                        +"\n"+
									            "    return b;"                                                        +"\n"+
									            "}"                                                                    +"\n"+
									            "void f2(){"                                                           +"\n"+
									            "     int a;"                                                          +"\n"+
									            "     a=f1();"                                                         +"\n"+
									            "     char buffer[a];"                                                 +"\n"+
									            "     strcpy(buffer,\"1234567890\");"                                    +"\n"+
									            "     //strncat(buffer,\"1234567890\",a);"                               +"\n"+
									            "     }"                                                               
									            ,
									            "gcc"
									            ,
									            "BO"
									            ,
									            },
//////////////////////////24//////////////////////////////////////////////
									            {
										            "#include <string.h>"                                                  +"\n"+
										            ""                                                                     +"\n"+
										            "int f1(){"                                                            +"\n"+
										            "    int a=3,b;"                                                       +"\n"+
										            "    if(a==3) b=9;"                                                   +"\n"+
										            "    else b=10;"                                                        +"\n"+
										            "    return b;"                                                        +"\n"+
										            "}"                                                                    +"\n"+
										            "void f2(){"                                                           +"\n"+
										            "     int a;"                                                          +"\n"+
										            "     a=f1();"                                                         +"\n"+
										            "     char buffer[9];"                                                 +"\n"+
										            "     //strcpy(buffer,\"1234567890\");"                                    +"\n"+
										            "     strncat(buffer,\"1234567890\",a);"                               +"\n"+
										            "     }"                                                               
										            ,
										            "gcc"
										            ,
										            "BO"
										            ,
										            },
//////////////////////////25//////////////////////////////////////////////
										            {
											            "#include <string.h>"                                                  +"\n"+
											            ""                                                                     +"\n"+
											            "int f1(){"                                                            +"\n"+
											            "    int a=3,b;"                                                       +"\n"+
											            "    if(a==3) b=9;"                                                   +"\n"+
											            "    else b=10;"                                                        +"\n"+
											            "    return b;"                                                        +"\n"+
											            "}"                                                                    +"\n"+
											            "void f2(){"                                                           +"\n"+
											            "     int a;"                                                          +"\n"+
											            "     a=f1();"                                                         +"\n"+
											            "     char buffer[10];"                                                 +"\n"+
											            "     //strcpy(buffer,\"1234567890\");"                                    +"\n"+
											            "     strncat(buffer,\"1234567890\",a);"                               +"\n"+
											            "     }"                                                               
											            ,
											            "gcc"
											            ,
											            "OK"
											            ,
											            },	

//////////////////////////26//////////////////////////////////////////////
											            {
												            "#include <string.h>"                                                  +"\n"+
												            ""                                                                     +"\n"+
												            "int all=7;"                                                           +"\n"+
												            "void f3(){"                                                           +"\n"+
												            "     all=8;"                                                          +"\n"+
												            "     }"                                                               +"\n"+
												            "void f4(){"                                                           +"\n"+
												            "     char buffer[8];"                                                 +"\n"+
												            "     f3();"                                                         +"\n"+
												            "     strncat(buffer,\"123456789\",all);"                                +"\n"+
												            "     }"                                                               
												            ,
												            "gcc"
												            ,
												            "BO"
												            ,
												            },
////////////////////////////27////////////////////////////////////////	
												            {
													            "#include <string.h>"                                                  +"\n"+
													            ""                                                                     +"\n"+
													            "int a=8;"                                                           +"\n"+
													            "void f3(){"                                                           +"\n"+
													            "     a=7;"                                                          +"\n"+
													            "     }"                                                               +"\n"+
													            "void f4(){"                                                           +"\n"+
													            "     char buffer[8];"                                                 +"\n"+
													            "     f3();"                                                           +"\n"+
													            "     strncat(buffer,\"123456789\",a);"                                +"\n"+
													            "     }"                                                               
													            ,
													            "gcc"
													            ,
													            "OK"
													            ,
													            },	
//////////////////////////28//////////////////////////////////////////////
													            {
														            "#include <string.h>"                                                  +"\n"+
														            ""                                                                     +"\n"+
														            "void f()"                                                             +"\n"+
														            "{"                                                                    +"\n"+
														            "     int i=0;"                                                        +"\n"+
														            "     for(;i<10;i++){"                                                 +"\n"+
														            "     if(i==5)"                                                        +"\n"+
														            "             break;"                                                  +"\n"+
														            "     }"                                                               +"\n"+
														            "     char buffer[i];"                                                 +"\n"+
														            "     strcpy(buffer,\"123456\");"                                        +"\n"+
														            "}"                                                                    
														            ,
														            "gcc"
														            ,
														            "BO"
														            ,
														            },
//////////////////////////29//////////////////////////////////////////////
														            {
															            "#include <string.h>"                                                  +"\n"+
															            "void f()"                                                             +"\n"+
															            "{"                                                                    +"\n"+
															            "     int i=10,j=0;"                                                   +"\n"+
															            "     if(i<8)"                                                         +"\n"+
															            "            j++;"                                                     +"\n"+
															            "     if(i>=8)"                                                        +"\n"+
															            "             i=(j==1?10:9);"                                          +"\n"+
															            "     char  buffer[i];"                                                +"\n"+
															            "     strcpy(buffer,\"123456789\");"                                     +"\n"+
															            "     }"                                                               
															            ,
															            "gcc"
															            ,
															            "BO"
															            ,
															            },
//////////////////////////30移到OOB中//////////////////////////////////////////////
		
		                {
		                "#include <stdio.h>"                                                   +"\n"+
		                ""                                                                     +"\n"+
		                "void zk_bo_10_f1()"                                                   +"\n"+
		                "{"                                                                    +"\n"+
		                "	char buf[3];"                                                        +"\n"+
		                "	int i = 10;"                                                         +"\n"+
		                ""                                                                     +"\n"+
		                "	printf(\"%c\", *(buf-1)); //DEFECT"                                    +"\n"+
		                "	printf(\"%c\", buf[4]); //DEFECT"                                      +"\n"+
		                " 	printf(\"%c\", *(buf + 10)); //DEFECT"                                +"\n"+
		                " 	(buf + i)[0] = 'a'; //DEFECT"                                       +"\n"+
		                "}"                                                                    
		                ,
		                "gcc"
			            ,
		                "OK"
		                ,
		                },
////////////////////////////31////////////////////////////////////////	
		                {
				            "#include <string.h>"                                                  +"\n"+
				            ""                                                                     +"\n"+
				            "void f()"                                                             +"\n"+
				            "{"                                                                    +"\n"+
				            "     int i=0;"                                                        +"\n"+
				            "     while(i<10){"                                                    +"\n"+
				            "     if(i==5)"                                                        +"\n"+
				            "             break;"                                                  +"\n"+
				            "	i++;"                                                                +"\n"+
				            "     }"                                                               +"\n"+
				            "     char buffer[i];"                                                 +"\n"+
				            "     strcpy(buffer,\"123456\");"                                        +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "BO"
				            ,
				            },	
//////////////////////////32移到OOB中//////////////////////////////////////////////	
		                {
		                "void zk_bo_12_f1()"                                                   +"\n"+
		                "{"                                                                    +"\n"+
		                "	char *addr[5];"                                                      +"\n"+
		                "	char buf[10];"                                                       +"\n"+
		                ""                                                                     +"\n"+
		                "	addr[0] = buf;"                                                      +"\n"+
		                "	(addr[0])[1024] = 'a'; //DEFECT"                                     +"\n"+
		                "	return;"                                                             +"\n"+
		                "}"                                                                    
		                ,
		                "gcc"
			            ,
		                "OK"
		                ,
		                },
////////////////////////////33移到OOB中////////////////////////////////////////	
		                {
		                "char* zk_bo_11_f1(char *ptr)"                                         +"\n"+
		                "{"                                                                    +"\n"+
		                "	return ptr;"                                                         +"\n"+
		                "}"                                                                    +"\n"+
		                ""                                                                     +"\n"+
		                "void zk_bo_11_f2()"                                                   +"\n"+
		                "{"                                                                    +"\n"+
		                "	char buf[10];"                                                       +"\n"+
		                ""                                                                     +"\n"+
		                "	(zk_bo_11_f1(buf))[1024] = 'a'; //DEFECT"                            +"\n"+
		                "	return;"                                                             +"\n"+
		                "}"                                                                    
		                ,
		                "gcc"
			            ,
		                "OK"
		                ,
		                },
//////////////////////////34//////////////////////////////////////////////	
		                {
				            "#include  <stdio.h>"                                                  +"\n"+
				            "int all=8;"                                                           +"\n"+
				            "void f()"                                                             +"\n"+
				            "{"                                                                    +"\n"+
				            "     all=6;"                                                          +"\n"+
				            "}"                                                                    +"\n"+
				            "void f1(){"                                                           +"\n"+
				            "     f();"                                                            +"\n"+
				            "     char buffer[all];"                                               +"\n"+
				            "     scanf(\"%7s\",buffer);"                                            +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "BO"
				            ,
				            },	
//////////////////////////35移到OOB中//////////////////////////////////////////////
		                {
		                "void zk_bo_14_f1()"                                                   +"\n"+
		                "{"                                                                    +"\n"+
		                "	int flag;"                                                           +"\n"+
		                "	char buf[10];"                                                       +"\n"+
		                ""                                                                     +"\n"+
		                "	flag = 1;"                                                           +"\n"+
		                "	if (flag)"                                                           +"\n"+
		                "	{"                                                                   +"\n"+
		                "		buf[20] = 'a'; //DEFECT"                                            +"\n"+
		                "	}"                                                                   +"\n"+
		                "	return;"                                                             +"\n"+
		                "}"                                                                    
		                ,
		                "gcc"
			            ,
		                "OK"
		                ,
		                },
//////////////////////////36//////////////////////////////////////////////
		                {
		                "#include <iostream>"                                                  +"\n"+
		                ""                                                                     +"\n"+
		                "using namespace std;"                                                 +"\n"+
		                ""                                                                     +"\n"+
		                "void zk_bo_15_f1()"                                                   +"\n"+
		                "{"                                                                    +"\n"+
		                "	char* buf=new char[11];"                                             +"\n"+
		                ""                                                                     +"\n"+
		                "	cin >> buf; //DEFECT"                                                +"\n"+
		                "	return;"                                                             +"\n"+
		                "}"                                                                    
		                ,
		                "gcc"
			            ,
		                "BO"
		                ,
		                },
///////////////////////////37////////////////////////////////////////	
		                {
		                "#include <stdio.h>"                                                   +"\n"+
		                "#include <stdlib.h>"                                                  +"\n"+
		                "#include <Windows.h>"                                                 +"\n"+
		                ""                                                                     +"\n"+
		                "void zk_bo_16_f1(FILE *fp, HINSTANCE HInstance)"                      +"\n"+
		                "{"                                                                    +"\n"+
		                "	char buf[10];"                                                       +"\n"+
		                "	char *ptr = buf;"                                                    +"\n"+
		                ""                                                                     +"\n"+
		                "	gets(buf); //DEFECT"                                                 +"\n"+
		                "	ptr = getenv(\"PATH\"); //DEFECT"                                      +"\n"+
		                "	LoadString(HInstance, 0, buf, 1024); //DEFECT"                       +"\n"+
		                "	fgets(buf, 1024, fp); //DEFECT"                                      +"\n"+
		                "	fread(buf, 1024, 1, fp); //DEFECT"                                   +"\n"+
		                "	return;"                                                             +"\n"+
		                "}"                                                                    
		                ,
		                "gcc"
			            ,
		                "BO"
		                ,
		                },
//////////////////////////38//////////////////////////////////////////////
		                //这个应该是添加摘要的吧   nmh
		                {
		                "#include <stdlib.h>"                                                  +"\n"+
		                "#include <string.h>"                                                  +"\n"+
		                ""                                                                     +"\n"+
		                "#define BUFSIZE 2"                                                    +"\n"+
		                ""                                                                     +"\n"+
		                "int main(int argc, char *argv[])"                                     +"\n"+
		                "{"                                                                    +"\n"+
		                "	char *buf;"                                                          +"\n"+
		                ""                                                                     +"\n"+
		                "	buf = (char *)malloc(BUFSIZE);"                                      +"\n"+
		                "	if (buf == NULL)"                                                    +"\n"+
		                "		return -1;"                                                         +"\n"+
		                "	strcpy(buf, argv[1]); //DEFECT"                                      +"\n"+
		                "	free(buf);"                                                          +"\n"+
		                "	return 0;"                                                           +"\n"+
		                "}"                                                                    
		                ,
		                "gcc"
			            ,
		                "OK"
		                ,
		                },
//////////////////////////39//////////////////////////////////////////////
		                {
		                "void zk_bo_17_f1()"                                                   +"\n"+
		                "{"                                                                    +"\n"+
		                "	int buf[] = {1, 2, 3, 4, 5, 6};"                                     +"\n"+
		                ""                                                                     +"\n"+
		                "	delete[] buf; //DEFECT"                                              +"\n"+
		                "	return;"                                                             +"\n"+
		                "}"                                                                    +"\n"+
		                ""                                                                     +"\n"+
		                "void zk_bo_17_f2(int flag)"                                           +"\n"+
		                "{"                                                                    +"\n"+
		                "	int buf[] = {1, 2, 3, 4, 5, 6};"                                     +"\n"+
		                "	int *ptr = buf;"                                                     +"\n"+
		                ""                                                                     +"\n"+
		                "	if (flag)"                                                           +"\n"+
		                "		ptr = new int[6];"                                                  +"\n"+
		                ""                                                                     +"\n"+
		                "	delete[] ptr; //DEFECT"                                              +"\n"+
		                "}"                                                                    
		                ,
		                "gcc"
			            ,
		                "BO"
		                ,
		                },
/////////////////  40  K8中未通过的用例 ///////////////////	
		   
		                {
		                "#include <stdlib.h>"                                                  +"\n"+
		                "#include <stdio.h>"                                                   +"\n"+
		                "void foo(const char *src)"                                            +"\n"+
		                "  {"                                                                  +"\n"+
		                "	char buf[20];"                                                       +"\n"+
		                "	snprintf(buf, sizeof(buf), \"%s\", src);  /* OK! */"                   +"\n"+
		                "	snprintf(buf, 40, \"%s\", src);  // SV.STRBO.BOUND_SPRINTF"            +"\n"+
		                "  }"                                                                  
		                ,
		                "gcc"
			            ,
		                "BO"
		                ,
		                },				               
		 });
}
}

