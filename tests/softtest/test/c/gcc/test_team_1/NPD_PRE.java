package softtest.test.c.gcc.test_team_1;

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
public class NPD_PRE extends ModelTestBase {
	public NPD_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD_PRE-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/npd_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
		        	/////////////////  0   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "char ghx_npd_11_f11()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *ptr=NULL;"                                                     +"\n"+
		            "	char *ph;"                                                           +"\n"+
		            "	int i=1;"                                                            +"\n"+
		            "    ph=(char *)memchr(ptr,'p',10);//DEFECT"                           +"\n"+
		            "    ph[i]=0;//DEFECT"                                                 +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                 
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  1   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_11_f10 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char * pch;"                                                        +"\n"+
		            "  char str[] = \"Example string\";"                                     +"\n"+
		            "  int i=1;"                                                           +"\n"+
		            "  pch = (char*) memchr (str, 'p', strlen(str));//FP"                  +"\n"+
		            "  if (pch!=NULL)"                                                     +"\n"+
		            "    printf (\"'p' found at position %d.\\n\", pch-str+1);"               +"\n"+
		            "  else"                                                               +"\n"+
		            "    pch[i]=0;//FP"                                                    +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  2   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_12_f12 (int len1,int len2)"                               +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *str1=NULL;"                                                   +"\n"+
		            "  char *str2=NULL;"                                                   +"\n"+
		            "  int n;"                                                             +"\n"+
		            ""                                                                     +"\n"+
		            "  n=memcmp ( str1, str2, len1>len2?len1:len2 );//DEFECT"              +"\n"+
		            "  if (n>0) printf (\"'%s' is greater than '%s'.\\n\",str1,str2);"        +"\n"+
		            "  else if (n<0) printf (\"'%s' is less than '%s'.\\n\",str1,str2);"      +"\n"+
		            "  else printf (\"'%s' is the same as '%s'.\\n\",str1,str2);"             +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  3   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_12_f11 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char str1[]=\"abcdefg\";"                                             +"\n"+
		            "  char str2[]=\"abc\";"                                                 +"\n"+
		            "  int n;"                                                             +"\n"+
		            "  int len1, len2;"                                                    +"\n"+
		            "  len1=strlen(str1);"                                                 +"\n"+
		            "  len2=strlen(str2);"                                                 +"\n"+
		            "  n=memcmp ( str1, str2, len1>len2?len1:len2 );//FP"                  +"\n"+
		            "  if (n>0) printf (\"'%s' is greater than '%s'.\\n\",str1,str2);"        +"\n"+
		            "  else if (n<0) printf (\"'%s' is less than '%s'.\\n\",str1,str2);"      +"\n"+
		            "  else printf (\"'%s' is the same as '%s'.\\n\",str1,str2);"             +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  4   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_13_f13(char *str5,char*str6)"                             +"\n"+
		            "{"                                                                    +"\n"+
		            "char *str1=NULL;"                                                     +"\n"+
		            "char *str2=NULL;"                                                     +"\n"+
		            "char *str3=\"abcedfg\";"                                                +"\n"+
		            "char *str4[40];"                                                      +"\n"+
		            "memcpy(str1,str3,7);  //DEFECT"                                       +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  5   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_13_f13(char *str5,char*str6)"                             +"\n"+
		            "{"                                                                    +"\n"+
		            "char *str1=NULL;"                                                     +"\n"+
		            "char *str2=NULL;"                                                     +"\n"+
		            "char *str3=\"abcedfg\";"                                                +"\n"+
		            "char *str4[40];"                                                      +"\n"+
		            "memcpy(str4,str2,10);  //DEFECT"                                      +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  6   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_13_f13(char *str5,char*str6)"                             +"\n"+
		            "{"                                                                    +"\n"+
		            "char *str1=NULL;"                                                     +"\n"+
		            "char *str2=NULL;"                                                     +"\n"+
		            "char *str3=\"abcedfg\";"                                                +"\n"+
		            "char *str4[40];"                                                      +"\n"+
		            "memcpy(str5,str6,strlen(str6)); //DEFECT"                             +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  7   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_13_f12 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char str1[]=\"Sample string\";"                                       +"\n"+
		            "  char str2[40];"                                                     +"\n"+
		            "  char str3[40];"                                                     +"\n"+
		            "  memcpy (str2,str1,strlen(str1)+1);//FP"                             +"\n"+
		            "  printf (\"str1: %s\\nstr2: %s\\nstr3: %s\\n\",str1,str2,str3);"          +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  8   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_13_f12 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char str1[]=\"Sample string\";"                                       +"\n"+
		            "  char str2[40];"                                                     +"\n"+
		            "  char str3[40];"                                                     +"\n"+
		            "  memcpy (str3,\"copy successful\",16);//FP"                            +"\n"+
		            "  printf (\"str1: %s\\nstr2: %s\\nstr3: %s\\n\",str1,str2,str3);"          +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  9   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_15_f15()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char *str=NULL;"                                                      +"\n"+
		            "memset(str,'*',6);//DEFECT"                                           +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  10   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_15_f14()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char str[]=\"welcome to beijing\";"                                     +"\n"+
		            "memset(str,'*',7);//FP"                                               +"\n"+
		            "printf(\"%s\\n\",str);"                                                  +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  11   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <math.h>"                                                    +"\n"+
		            "int ghx_npd_17_f17() "                                                +"\n"+
		            "{ "                                                                   +"\n"+
		            "double fraction;"                                                     +"\n"+
		            "double *integer=NULL; "                                               +"\n"+
		            "double number = 100000.567; "                                         +"\n"+
		            "fraction = modf(number, integer); //DEFECT"                           +"\n"+
		            "return 0; "                                                           +"\n"+
		            "} "                                                                   
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  12   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <math.h>"                                                    +"\n"+
		            "int ghx_npd_17_f16() "                                                +"\n"+
		            "{ "                                                                   +"\n"+
		            "double fraction, integer; "                                           +"\n"+
		            "double number = 100000.567; "                                         +"\n"+
		            "fraction = modf(number, &integer); //FP"                              +"\n"+
		            "printf(\"The whole and fractional parts of %lf are %lf and %lf\\n\", number, integer, fraction); "                                         +"\n"+
		            ""                                                                     +"\n"+
		            "return 0; "                                                           +"\n"+
		            "} "                                                                   
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  13   ///////////////////
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_20_f20 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  char c;"                                                            +"\n"+
		            ""                                                                     +"\n"+
		            "  pFile=fopen(\"alphabet.txt\",\"wt\");"                                  +"\n"+
		            "    for (c = 'A' ; c <= 'Z' ; c++)"                                   +"\n"+
		            "    {"                                                                +"\n"+
		            "    putc (c , pFile);//DEFECT"                                        +"\n"+
		            "    }"                                                                +"\n"+
		            "  fclose (pFile); //DEFECT"                                           +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  14   ///////////////////
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_20_f19()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "FILE * pFile;"                                                        +"\n"+
		            "  char c;"                                                            +"\n"+
		            ""                                                                     +"\n"+
		            "  pFile=fopen(\"alphabet.txt\",\"wt\");"                                  +"\n"+
		            "    for (c = 'A' ; c <= 'Z' ; c++)"                                   +"\n"+
		            "	{"                                                                   +"\n"+
		            "		if(pFile!=NULL)"                                                    +"\n"+
		            "		{"                                                                  +"\n"+
		            "		putc(c,pFile);//FP"                                                 +"\n"+
		            "		fclose(pFile);"                                                     +"\n"+
		            "		}"                                                                  +"\n"+
		            "	}"                                                                   +"\n"+
		            "		return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  15   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_19_f1(char c)"                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	FILE *fp = NULL;"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "	ungetc(c, fp); //DEFECT"                                             +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  16   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_19_f2(FILE *fp)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (fp == NULL)"                                                     +"\n"+
		            "		return;"                                                            +"\n"+
		            "	ungetc((int)'a', fp); //FP"                                          +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  17   ///////////////////
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_18_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	FILE *fp;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	fp = tmpfile();"                                                     +"\n"+
		            "	fputc((int)'a', fp); //DEFECT"                                       +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  18   ///////////////////
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_18_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	FILE *fp;"                                                           +"\n"+
		            "	fp = tmpfile();"                                                     +"\n"+
		            "	if (fp != NULL)"                                                     +"\n"+
		            "		fputc((int)'a', fp); //FP"                                          +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  19   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_17_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *des = NULL;"                                                   +"\n"+
		            "	char *src = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	strxfrm(des, src, 5); //DEFECT"                                      +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  20   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_17_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char des[10];"                                                       +"\n"+
		            "	char src[] = \"sample\";"                                              +"\n"+
		            ""                                                                     +"\n"+
		            "	strxfrm(des, src, sizeof(src)); //FP"                                +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  21   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_15_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	strtoul(str, NULL, 2); //DEFECT"                                     +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  22   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void zk_npd_15_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"2009 123\";"                                            +"\n"+
		            ""                                                                     +"\n"+
		            "	strtoul(str, NULL, 10); //FP"                                        +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  23   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_14_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"This is a sample\";"                                    +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strtok(str, NULL); //DEFECT"                                   +"\n"+
		            "	printf(\"%s\", pch); //DEFECT"                                         +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            }, 
		        	/////////////////  24   ///////////////////
		            //hcj次测试用例应该报NPD_PRE (函数strtok第一参数为NULL)
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_14_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"This is a sample\";"                                    +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strtok(str, \" \"); //FP"                                        +"\n"+
		            "	while (pch != NULL)"                                                 +"\n"+
		            "	{"                                                                   +"\n"+
		            "		printf(\"%s\", pch); //FP"                                            +"\n"+
		            "		strtok(NULL, \" \"); //FP"                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            }, 
		        	/////////////////  25   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_14_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"This is a sample\";"                                    +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strtok(str, \" \"); //FP"                                        +"\n"+
		            "	while (pch != NULL)"                                                 +"\n"+
		            "	{"                                                                   +"\n"+
		            "		printf(\"%s\", pch); //FP"                                            +"\n"+
		            "		strtok(NULL, \" \"); //FP"                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "	printf(\"%s\", pch); //DEFECT"                                         +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            }, 
		        	/////////////////  26   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_12_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str = NULL;"                                                   +"\n"+
		            "	char *sub = NULL;"                                                   +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strstr(str, sub); //DEFECT"                                    +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  27   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_12_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"This is sample\";"                                      +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strstr(str, \"nothing\"); //FP"                                  +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  28   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_12_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"This is sample\";"                                      +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strstr(str, \"nothing\"); //FP"                                  +"\n"+
		            "	printf(\"%s\", pch); //DEFECT"                                         +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  29   ///////////////////	
		            //hcj全局变量的默认值为NOTNULL
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "char *zk_npd_11_g1 = NULL;"                                           +"\n"+
		            "char *zk_npd_11_g2 = NULL;"                                           +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_11_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	strspn(zk_npd_11_g1, zk_npd_11_g2); //DEFECT"                        +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  30   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "char *zk_npd_11_g1 = NULL;"                                           +"\n"+
		            "char *zk_npd_11_g2 = NULL;"                                           +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_11_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (zk_npd_11_g1 && zk_npd_11_g2)"                                   +"\n"+
		            "		strspn(zk_npd_11_g1, zk_npd_11_g2); //FP"                           +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  31   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_10_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str = NULL;"                                                   +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strrchr(str, 's'); //DEFECT"                                   +"\n"+
		            "	printf(\"%c\", *pch); //DEFECT"                                        +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  32   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_10_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"This is a sample\";"                                    +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strrchr(str, 's'); //FP"                                       +"\n"+
		            "	if (pch)"                                                            +"\n"+
		            "		printf(\"%c\", *pch); //FP"                                           +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  33   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_9_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str1, *str2;"                                                  +"\n"+
		            "	str1 = NULL;"                                                        +"\n"+
		            "	str2 = NULL;"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "	strpbrk(str1, str2); //DEFECT"                                       +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  34   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_9_f2()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            "	char str[] = \"This is sample\";"                                      +"\n"+
		            "	char key[] = \"xyz\";"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strpbrk(str, key); //FP"                                       +"\n"+
		            ""                                                                     +"\n"+
		            "	if (pch)"                                                            +"\n"+
		            "		printf(\"%c\", *pch); //FP"                                           +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  35   ///////////////////	
		            //hcj此处应报NPD
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_9_f2()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            "	char str[] = \"This is sample\";"                                      +"\n"+
		            "	char key[] = \"xyz\";"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strpbrk(str, key); //FP"                                       +"\n"+
		            "	printf(\"%c\", *pch); //DEFECT"                                        +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  36   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_8_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *des = NULL;"                                                   +"\n"+
		            "	char *src = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	strncpy(des, src, 4); //DEFECT"                                      +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  37   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_8_f2()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char des[10];"                                                       +"\n"+
		            "	char src[] = \"This is a sample\";"                                    +"\n"+
		            ""                                                                     +"\n"+
		            "	strncpy(des, src, 7); //FP"                                          +"\n"+
		            "	des[7] = '\\0';"                                                      +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  38   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_7_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str1 = NULL;"                                                  +"\n"+
		            "	char *str2 = NULL;"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "	strncmp(str1, str2, 5); //DEFECT"                                    +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  39   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_7_f2()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str1 = \"hello world\";"                                         +"\n"+
		            "	char *str2 = \"hello\";"                                               +"\n"+
		            ""                                                                     +"\n"+
		            "	strncmp(str1, str2, 5); //FP"                                        +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  40   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_6_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *des = NULL;"                                                   +"\n"+
		            "	char *src = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	strncat(des, src, 4); //DEFECT"                                      +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  41   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void zk_npd_6_f2()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char des[10] = \"This\";"                                              +"\n"+
		            "	char src[10] = \"is it and\";"                                         +"\n"+
		            ""                                                                     +"\n"+
		            "	strncat(des, src, 5); //FP"                                          +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  42   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_5_f1(char *str)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	strlen(str); //DEFECT"                                               +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  43   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_5_f2(char *str)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (!str)"                                                           +"\n"+
		            "		return;"                                                            +"\n"+
		            "	strlen(str); //FP"                                                   +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  44   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_3_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str1 = NULL;"                                                  +"\n"+
		            "	char *str2 = NULL;"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "	strcspn(str1, str2); //DEFECT"                                       +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  45   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_3_f2()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str1 = \"abcdefg\";"                                             +"\n"+
		            "	char *str2 = \"gh\";"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "	strcspn(str1, str2); //FP"                                           +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  46   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_14_f14()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char *str1=NULL;"                                                     +"\n"+
		            "char *str2=NULL;"                                                     +"\n"+
		            "memmove(str1,str2,10);//DEFECT"                                       +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  47   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_14_f13()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char *dest = \"abcdefghijklmnopqrstuvwxyz0123456789\"; "                +"\n"+
		            "char *src = \"******************************\"; "                       +"\n"+
		            ""                                                                     +"\n"+
		            "memmove(dest, src, 26); //FP"                                         +"\n"+
		            "printf(\"%s\\n\", dest); "                                               +"\n"+
		            "return 0; "                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  48   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_21_f21 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *string = NULL;"                                               +"\n"+
		            "  puts (string);//DEFECT"                                             +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  49   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_21_f20()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char *string=\"welcome to beijing\";"                                   +"\n"+
		            "puts (string);//FP"                                                   +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  50   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_22_f22 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *str=NULL;"                                                    +"\n"+
		            "  strcat (str,\"strings \");//DEFECT"                                   +"\n"+
		            ""                                                                     +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  51   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "int ghx_npd_22_f21 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char str[80];"                                                      +"\n"+
		            "  strcpy (str,\"these \");//FP"                                         +"\n"+
		            "  strcat (str,\"strings \");//FP"                                       +"\n"+
		            "  strcat (str,\"are \");//FP"                                           +"\n"+
		            "  strcat (str,\"concatenated.\");//FP"                                  +"\n"+
		            "  puts (str);"                                                        +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  52   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void jhb_npd_10_f1(char* str){"                                       +"\n"+
		            "	float f;"                                                            +"\n"+
		            "    f=atof(str);      //DEFECT"                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  53   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int jhb_npd_10_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	float t;"                                                            +"\n"+
		            "	char *str=\"12345.67\";"                                               +"\n"+
		            "	t=atof(str);       //FT"                                             +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  54   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void jhb_npd_11_f1(){"                                                +"\n"+
		            "	char a[]=\"-100\";"                                                    +"\n"+
		            "    char *b;"                                                         +"\n"+
		            "	b=NULL;"                                                             +"\n"+
		            "	int c;"                                                              +"\n"+
		            "	c=atoi(a)+atoi(b);  //DEFECT"                                        +"\n"+
		            "	printf(\"c=%d\\n\",c);"                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  55   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void jhb_npd_11_f2()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	char a[]=\"-100\";"                                                    +"\n"+
		            "	char b[]=\"456\";"                                                     +"\n"+
		            "	int c;"                                                              +"\n"+
		            "	c=atoi(a)+atoi(b);  //FT"                                            +"\n"+
		            "	printf(\"c=%d\\n\",c);"                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  56   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_1_f1(char *str1, char *str2)"                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	strcoll(str1, str2); //DEFECT"                                       +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  57   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_1_f2()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str1 = \"This is first\";"                                       +"\n"+
		            "	char *str2 = \"Second\";"                                              +"\n"+
		            ""                                                                     +"\n"+
		            "	strcoll(str1, str2); //FP"                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		            
		            
		            
		            
		 });
	 }
}
