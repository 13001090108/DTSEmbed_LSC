package softtest.test.gcc.rules.fault;

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
public class Test_NPD_CHECK extends ModelTestBase {
	public Test_NPD_CHECK(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD_CHECK-0.1.xml";
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
	///////////////  0   ///////////////////	
		            {
		            "void func(int a[], int len)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "    int *p;"                                                          +"\n"+
		            "    p=(int *)malloc(len*4);"                                          +"\n"+
		            "	int i=0;    "                                                        +"\n"+
		            "	for(i=0;i<len;i++)"                                                  +"\n"+
		            "       *(p+i)=a[i];"                                                  +"\n"+
		            "    *p=1;"                                                            +"\n"+
		            "    if(!p)"                                                           +"\n"+
		            "		return;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_Check"
		            ,
		            },

	/////////////////  1   本来应该报的，但是目前未把q->zdevice识别成一个整体的变量 ///////////////////	
		            {
		            "#include<stdio.h>"                                                    +"\n"+
		            "#include<stdlib.h>"                                                   +"\n"+
		            "struct ssysdep_conn"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            " int o;"                                                              +"\n"+
		            " char *zdevice;"                                                      +"\n"+
		            "}"                                                                    +"\n"+
		            "void zbufcpy()"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            " } "                                                                  +"\n"+
		            "int open(char *q, int k)"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "  return k=0;"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void test(char *p)"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "  struct ssysdep_conn *q;"                                            +"\n"+
		            "  int k = 0;"                                                         +"\n"+
		            "  q = (struct ssysdep_conn *) malloc (sizeof (struct ssysdep_conn));" +"\n"+
		            "  q->zdevice = zbufcpy (p);"                                          +"\n"+
		          //  "  if(k<0) "                                                           +"\n"+
		            "   char c=*(q->zdevice);//defect "                                +"\n"+		          
		            "  for (k=0;k<5 && q->zdevice != NULL;k++)"                            +"\n"+
		            "  {"                                                                  +"\n"+
		            "       k++;"                                                          +"\n"+
		            "  }"                                                                  +"\n"+
		              ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },

      /////////////////  2   ///////////////////	

				 {
			            "struct sconnection"                                                   +"\n"+
			            "{"                                                                    +"\n"+
			            "  "                                                                   +"\n"+
			            "  int num;"                                                           +"\n"+
			            "  struct uuconf_port *qport;"                                         +"\n"+
			            ""                                                                     +"\n"+
			            "};"                                                                   +"\n"+
			            ""                                                                     +"\n"+
			            "struct uuconf_port"                                                   +"\n"+
			            "{"                                                                    +"\n"+
			            " "                                                                    +"\n"+
			            ""                                                                     +"\n"+
			            "char *uuconf_zname;"                                                  +"\n"+
			            "  "                                                                   +"\n"+
			            " union"                                                               +"\n"+
			            "    {"                                                                +"\n"+
			            "  "                                                                   +"\n"+
			            "   char  **uuconf_smodem;"                           +"\n"+
			            "   "                                                                  +"\n"+
			            "   char *mode;"                                                       +"\n"+
			            "  } uuconf_u;"                                                        +"\n"+
			            "};"                                                                   +"\n"+
			            ""                                                                     +"\n"+
			            "void test(struct sconnection *qconn)"                                 +"\n"+
			            "{  "                                                                  +"\n"+
			            "  char **pzdialer;"                                                   +"\n"+
			            ""                                                                     +"\n"+
			            "  pzdialer = qconn->qport->uuconf_u.uuconf_smodem;"   +"\n"+
			            "  if (qconn->qport == NULL)"                                          +"\n"+
			            "      return;"                                                        +"\n"+
			            ""                                                                     +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "NPD_Check"
			            ,
			            },
	/////////////////  3   ///////////////////	
		            {
		            "struct sconnection"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "  "                                                                   +"\n"+
		            "  int num;"                                                           +"\n"+
		            "  struct uuconf_port *qport;"                                         +"\n"+
		            ""                                                                     +"\n"+
		            "};"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "struct uuconf_port"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            " "                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "char *uuconf_zname;"                                                  +"\n"+
		            "  "                                                                   +"\n"+
		            " union"                                                               +"\n"+
		            "    {"                                                                +"\n"+
		            "  "                                                                   +"\n"+
		            "   struct uuconf_modem_port uuconf_smodem;"                           +"\n"+
		            "   "                                                                  +"\n"+
		            "   char *mode;"                                                       +"\n"+
		            "  } uuconf_u;"                                                        +"\n"+
		            "};"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "struct uuconf_modem_port"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            " "                                                                    +"\n"+
		            "    char **uuconf_pzdialer;"                                          +"\n"+
		            "    char *uuconf_zdevice"                                             +"\n"+
		            "};"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void test(struct sconnection *qconn)"                                 +"\n"+
		            "{  "                                                                  +"\n"+
		            "  char **pzdialer;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "  pzdialer = qconn->qport->uuconf_u.uuconf_smodem.uuconf_pzdialer;"   +"\n"+
		            "  if (qconn->qport == NULL)"                                          +"\n"+
		            "      return;"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_Check"
		            ,
		            },
	/////////////////  4  ///////////////////	
			            {
			            "#include <stdio.h>"                                                   +"\n"+
			            "#include <stdlib.h>"                                                  +"\n"+
			            "struct Student"                                                       +"\n"+
			            "{"                                                                    +"\n"+
			            "   int age;"                                                          +"\n"+
			            "   int number;"                                                       +"\n"+
			            "}student;"                                                            +"\n"+
			            ""                                                                     +"\n"+
			            "int main(int argc, char *argv[])"                                     +"\n"+
			            "{"                                                                    +"\n"+
			            " int i;"                                                 +"\n"+

			            "  struct Student *p;"                                                 +"\n"+
			            "  p=&student;"                                                        +"\n"+
			            "  p->age = 10;"                                                        +"\n"+
			            "  while(p && (p->age!=0))"                                            +"\n"+
			          //  "  p->age = 0;"                                                        +"\n"+
			            "  system(\"PAUSE\");	"                                                  +"\n"+
			            "  return 0;"                                                          +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "NPD_Check"
			            ,
			            },
	/////////////////  4   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(char*);"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(char *ptr)"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	*ptr = 'a';"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "	if(ptr != 0) {"                                                          +"\n"+
		            "		*ptr = 'b';"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_Check"
		            ,
		            },
		        	/////////////////  5   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(char* p) { *p =5;}"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(char *ptr)"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	func2(ptr);"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "	if(ptr != 0) {"                                                          +"\n"+
		            "		*ptr = 'b';"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_Check"
		            ,
		            },      
	/////////////////  6   ///////////////////	
		            {
		            "void f(int **p)"                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "    int a = **p;"                                                     +"\n"+
		            "    if(*p == NULL)"                                                   +"\n"+
		            "    {"                                                                +"\n"+
		            "    }"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  7   ///////////////////	
		            {
		            "void f(int *p, int *q)"                                               +"\n"+
		            "{"                                                                    +"\n"+
		            "    *p= 5;"                                                           +"\n"+
		            "    if(p==q)"                                                         +"\n"+
		            "    {"                                                                +"\n"+
		            "    }"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  8   ///////////////////	
		            {
		            "struct ssfilename"                                                    +"\n"+
		            "{  "                                                                  +"\n"+
		            "	char *zfile;"                                                        +"\n"+
		            "	char bgrade;"                                                        +"\n"+
		            " 	char bdummy;"                                                       +"\n"+
		            "};"                                                                   +"\n"+
		            "static struct ssfilename *asSwork_files;"                             +"\n"+
		            ""                                                                     +"\n"+
		            "int fswork_file()"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "   return 1;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            "int bsearch()"                                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "   return 0;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            "void testNpd_check()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            " int k=0;"                                                            +"\n"+
		           "   asSwork_files[k].zfile = \"hello world\";	"                         +"\n"+
		           " if(!fswork_file()||( asSwork_files!=NULL && bsearch()!=NULL))"       +"\n"+
		            "    k =1;"                                                            +"\n"+
		           
		           "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_Check"
		            ,
		            },
	/////////////////  4  ///////////////////	
				            {
				            "#include <stdio.h>"                                                   +"\n"+
				            "#include <stdlib.h>"                                                  +"\n"+
				            "struct Student"                                                       +"\n"+
				            "{"                                                                    +"\n"+
				            "   int age;"                                                          +"\n"+
				            "   int* next;"                                                       +"\n"+
				            "};"                                                            +"\n"+
				            ""                                                                     +"\n"+
				            "int main(struct Student *s)"                                     +"\n"+
				            "{"                                                                    +"\n"+
				         	 "  struct Student *p;"                                                 +"\n"+
				          "  for(p=s;p!=null;p=p->next )"                                            +"\n"+
				          //  "  p->age = 0;"                                                        +"\n"+
				            "  system(\"PAUSE\");	"                                                  +"\n"+
				            "  return 0;"                                                          +"\n"+
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
