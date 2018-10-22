package softtest.test.c.gcc.expression;




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
public class BO_EXP extends ModelTestBase{
	public BO_EXP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/BO-0.1.xml";
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
		 return Arrays.asList(new Object[][] {
	/////////////////  0   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void GHX_BO_1_f1(char p[420])"                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer [400];"                                                  +"\n"+
		            "	strcpy (buffer,\"welcome to beijing \");//FP"                          +"\n"+
		            "	strcat (buffer, p);//DEFECT"                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void GHX_BO_2_f2(int aa, char *ab)//chh 指针数组暂不支持"                                 +"\n"+
		            " {"                                                                   +"\n"+
		            "     char Buffer[16];"                                                +"\n"+
		            "     if (aa == 1) {"                                                  +"\n"+
		            "     strcpy(Buffer, ab);//DEFECT"                                 +"\n"+
		            "             }"                                                       +"\n"+
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
		            "int ghx_bo_5_f5()"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "   FILE * File;"                                                      +"\n"+
		            "   char string [100];"                                                +"\n"+
		            ""                                                                     +"\n"+
		            "   File = fopen (\"myfile.txt\" , \"r\");"                                +"\n"+
		            " "                                                                    +"\n"+
		            "     fgets (string , 200 , File);//DEFECT"                            +"\n"+
		            "     puts (string);"                                                  +"\n"+
		            "     fclose (File);"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "   return 0;"                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "int ghx_bo_6_f6()"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "char str1[100];"                                                      +"\n"+
		            "char str2[50];"                                                       +"\n"+
		            "memcpy(str2,str1,(sizeof(str1)));//DEFECT"                            +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                 
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
////////////////	/  4  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_bo_6_f5()"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "char str1[100];"                                                      +"\n"+
		            "char str2[50];"                                                       +"\n"+
		            "memcpy(str2,str1,(sizeof(str2)));//FP"                                +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	///////////////// 5  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_bo_7_f7() "                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[16];"                                                       +"\n"+
		            "	snprintf(str, 20, \"%s %d\", \"hello worldxxxx\", 1000);//DEFECT"       +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	///////////////// 6  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <unistd.h>"                                                      +"\n"+
		            //"#include <conio.h>"                                                   +"\n"+
		            "//#include <libgen.h> "                                               +"\n"+
		            "void ghx_bo_8_f8(char *argv[],char a[3],char b[33],char ch)"          +"\n"+
		            "{"                                                                    +"\n"+
		            "FILE *fp;"                                                            +"\n"+
		            "int hand;"                                                            +"\n"+
		            "int i=0;"                                                             +"\n"+
		            " char *password;"                                                     +"\n"+
		            "char string [2];"                                                     +"\n"+
		            " fp = fopen (\"myfile.txt\" , \"r\");"                                    +"\n"+
		            "fgets(string,5,fp);//DEFECT"                                          +"\n"+
		            "fread(string,10,10,fp);//DEFECT"                                      +"\n"+
		            "read(hand,string,20);"                                        +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "while((ch = getchar()) != '\\n') "                                     +"\n"+
		            "  { "                                                                 +"\n"+
		            "  if(ch == -1) break; "                                               +"\n"+
		            "  string[i++] = ch; "                                                 +"\n"+
		            "  } "                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  7 ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_BO_9_f9()"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "char fixed_buf[10];"                                                  +"\n"+
		            "sprintf(fixed_buf,\"Very long format string\\n\");//DEFECT"              +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  8  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "void wrapped_read(char* buf, int count) "                             +"\n"+
		            "{"                                                                    +"\n"+
		            "fgets(buf, count, stdin);"                                            +"\n"+
		            "}"                                                                    +"\n"+
		            "void ghx_BO_10_f10()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char buf1[12];"                                                       +"\n"+
		            "char buf2[12];"                                                       +"\n"+
		            "char dst[16];"                                                        +"\n"+
		            "wrapped_read(buf1, sizeof(buf1));"                                    +"\n"+
		            "wrapped_read(buf2, sizeof(buf2));"                                    +"\n"+
		            "sprintf(dst, \"%s-%s\\n\", buf1, buf2);//DEFECT"                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  9 ///////////////////	
		            {
		            "#include <unistd.h> "                                                      +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "void ghx_bo_11_f11()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char src[32];"                                                        +"\n"+
		            "char dst[48];"                                                        +"\n"+
		            "read(0, src, sizeof(src));"                                           +"\n"+
		            "strcpy(dst, src);//chh  FP"                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  10 ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "void ghx_bo_12_f12()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char s[4]; // small destination buffer"                               +"\n"+
		            "// create a file with a string of length 50"                          +"\n"+
		            "FILE* m_file = fopen(\"test.txt\", \"w\");"                               +"\n"+
		            "fprintf( m_file ,"                                                    +"\n"+
		            "\"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA\");"               +"\n"+
		            ""                                                                     +"\n"+
		            "// buffer overrun because width is set to incorrect length"           +"\n"+
		            "fscanf(m_file, \"%50s\", s);//DEFECT"                                   +"\n"+
		            "fclose(m_file);"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  11///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void ghx_bo_13_f13(FILE* f, char* x)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char tmp[100];"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "fscanf(f, \"%10s\", tmp);"                                              +"\n"+
		            "fscanf(f, \"%20s\", tmp);"                                              +"\n"+
		            "fscanf(f, \"%10s\", x);"                                                +"\n"+
		            "fscanf(f, \"%s\", x);//DEFECT"                                          +"\n"+
		            "fscanf(f, \"%%%s\", x);//DEFECT"                                        +"\n"+
		            "fscanf(f, \"%%%10s\", x);"                                              +"\n"+
		            "fscanf(f, \"%*s%s\", x);//DEFECT"                                       +"\n"+
		            "fscanf(f, \"%*s%10s\", x);"                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	///////////////// 12 ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "void ghx_bo_14_f14()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char str[4]=\"abc\";"                                                   +"\n"+
		            "gets(str);//DEFECT"                                                   +"\n"+
		            "printf(str);/*fault belongs to TD*/"                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  13  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void ghx_bo_15_f15()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char buf [20];"                                                       +"\n"+
		            "char long_src[30];"                                                   +"\n"+
		            "char *external_pointer;"                                              +"\n"+
		            "strncpy(buf, long_src, 30); //DEFECT"                                 +"\n"+
		            "strncpy(buf, external_pointer, sizeof(buf));//DEFECT"                 +"\n"+
		            "strncpy(buf, external_pointer, 30); //DEFECT"                         +"\n"+
		            "strncpy(buf, external_pointer, sizeof(buf)-1); //FP"                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  14  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_bo_16_f16()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char overflown_buf[20];"                                              +"\n"+
		            "gets(overflown_buf);//DEFECT"                                         +"\n"+
		            "gets(overflown_buf+1);//DEFECT"                                       +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  15  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "int ghx_bo_17_f17(char *POINTERbuf)"                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char FIXEDbuf[12];"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "strcpy(FIXEDbuf, \"Something rather large\");//DEFECT"                  +"\n"+
		            "strcpy(POINTERbuf, \"Something very large as well\");"                  +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  16  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void jhb_bo_1_f1(){"                                                  +"\n"+
		            "	char *strPathName = (char*)malloc(100*sizeof(char));"                +"\n"+
		            "	char s[3];"                                                          +"\n"+
		            "	strcpy(strPathName,\"\\\\Application\\\\MakeSheet\\\\*.pms\");  //FT"        +"\n"+
		            "	strcpy(s,\"\\\\\\\\\");  //FP"                                             +"\n"+
		            "	strcpy(s,\"\\\\\\\\\\\\*.*\");  //DEFECT"                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },

	/////////////////  17///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_13_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buf[10];"                                                       +"\n"+
		            "	char *str = \"This is a sample\";"                                     +"\n"+
		            ""                                                                     +"\n"+
		            "	strcpy(buf, str); //DEFECT"                                          +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  18  ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "#define BUFSIZE 2"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int main(int argc, char *argv[])//chh 指针数组暂不支持"                                     +"\n"+
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
	/////////////////  19   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_21_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buf[128];"                                                      +"\n"+
		            ""                                                                     +"\n"+
		            "	fscanf(stdin, \"%s\", buf); //DEFECT"                                  +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  20//////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_22_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buf[10];"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "	strcpy(buf, \"AAAAAAAAAAAA\"); //DEFECT"                               +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  21   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_23_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char src[] = \"ThisisSample\";"                                        +"\n"+
		            "	char des[6];"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "	strncpy(des, src, 6); //DEFECT"                                      +"\n"+
		            "	printf(\"%s\", des);"                                                  +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  22   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_25_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buf1[12];"                                                      +"\n"+
		            "	char buf2[12];"                                                      +"\n"+
		            "	char des[16];"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "	fgets(buf1, sizeof(buf1), stdin);"                                   +"\n"+
		            "	fgets(buf2, sizeof(buf2), stdin);"                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	sprintf(des, \"%s-%s\", buf1, buf2); //DEFECT"                         +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  23   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_26_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buf1[121];"                                                     +"\n"+
		            "	char buf2[16];"                                                      +"\n"+
		            "	int i;"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "	for (i = 0; i < 121; i++) {"                                         +"\n"+
		            "		buf1[i] = getchar();"                                               +"\n"+
		            "	}"                                                                   +"\n"+
		            "	strcpy(buf2, buf1); //DEFECT"                                        +"\n"+
		            "	printf(\"%s\\n\", buf1);"                                               +"\n"+
		            "	printf(\"%s\\n\", buf2);"                                               +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  24   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_27_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char s[4];"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	FILE* m_file = fopen(\"test.txt\", \"w\");"                              +"\n"+
		            "	fprintf( m_file ,"                                                   +"\n"+
		            "		\"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA\");"             +"\n"+
		            "	fclose(m_file);"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "	fscanf(m_file, \"%50s\", s); //DEFECT"                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  25   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_28_f1(FILE *fp)"                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	char tmp[50];"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "	fscanf(fp, \"%20s\", tmp);"                                            +"\n"+
		            "	fscanf(fp, \"%10s\", tmp);"                                            +"\n"+
		            "	fscanf(fp, \"%50s\", tmp); //DEFECT"                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  26   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "struct S{"                                                            +"\n"+
		            "   char a[12];"                                                       +"\n"+
		            "   char b[34];"                                                       +"\n"+
		            "}s1;"                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   strcpy(s1.a,s1.b);"                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },

	

 
		 });
	 }
}

