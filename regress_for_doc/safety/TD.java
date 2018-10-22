package safety;

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
import softtest.summary.lib.c.LibManager;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class TD extends ModelTestBase
{

	public TD(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath = "softtest/rules/gcc/safety/TD-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("safety");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		/*
		LIB_SUMMARYS_PATH="gcc_lib";
		libManager.loadLib(LIB_SUMMARYS_PATH);
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
		*/

	}

	@Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][]
				 {
				 
	/////////////////  1   ///////////////////	
		            {
		            "int func(int a, double b)"                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *s = getenv(\"ConFig_File\");"                                    +"\n"+
		            "	fopen(s, \"r\");"                                                      +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "TD"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "int func(double b)"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "    int arr[10];"                                                     +"\n"+
		            "    int c, a;"                                                        +"\n"+
		            "    scanf(\"%d\", &a);"                                                 +"\n"+
		            "    c = a;"                                                           +"\n"+
		            "    arr[a] = 10;"                                                     +"\n"+
		            "    return 0;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "TD"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "void func2()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "  char a[15];"                                                        +"\n"+
		            "  scanf(\"%s\",&a);"                                                    +"\n"+
		            "  system(a);"                                                         +"\n"+
		            "  return;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "TD"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "int func()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "    int a = 0;"                                                       +"\n"+
		            "    char s[100];"                                                     +"\n"+
		            "    gets(s);"                                                         +"\n"+
		            "    system(s);"                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "TD"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "int func2()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "    char *s = getenv(\"ConFig_File\");"                                 +"\n"+
		            "    if (strcmp(s, \"C:\\\\read.ini\") == 0) {"                            +"\n"+
		            "        fopen(s, \"r\");"                                               +"\n"+
		            "    }"                                                                +"\n"+
		            "    return 0;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "TD"
		            ,
		            },
	/////////////////  6   ///////////////////	
		            {
		            "int f2(char a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	char b[10];                "                                         +"\n"+
		            "	char c[20];"                                                         +"\n"+
		            "    	int i = 0; "                                                     +"\n"+
		            "	read(0,b,sizeof(b));"                                                +"\n"+
		            "	strcpy(c,b);"                                                        +"\n"+
		            "    return 0;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "TD"
		            ,
		            },
	/////////////////  7   ///////////////////	
		            {
		            "void func1() {"                                                       +"\n"+
		            "    char name[100];"                                                  +"\n"+
		            "    scanf(\"%s\", name);"                                               +"\n"+
		            "	gethostbyaddr(name);"                                                +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2() {"                                                       +"\n"+
		            "    char name[100];"                                                  +"\n"+
		            "    scanf(\"%s\", name);"                                               +"\n"+
		            "	gethostbyname(name);"                                                +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3() {"                                                       +"\n"+
		            "    char name[100];"                                                  +"\n"+
		            "    scanf(\"%s\", name);"                                               +"\n"+
		            "	sethostname(name);"                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "TD"
		            ,
		            },
	/////////////////  8   ///////////////////	
		            {
		            "void func1(void* socket) {"                                           +"\n"+
		            "     char manager[10];"                                               +"\n"+
		            "     int result;"                                                     +"\n"+
		            "     fgets(manager, sizeof(manager), socket);"                        +"\n"+
		            ""                                                                     +"\n"+
		            "     if ( ( rc = ldap_search_ext_s( ld, FIND_DN, LDAP_SCOPE_BASE,"    +"\n"+
		            "       manager, 0, 0, 0, 0, LDAP_NO_LIMIT, "                          +"\n"+
		            "       LDAP_NO_LIMIT, &result ) ) == 0 ) {"                           +"\n"+
		            "		int i;"                                                             +"\n"+
		            "		i = 0;"                                                             +"\n"+
		            "     }"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "TD"
		            ,
		            },
	/////////////////  9   ///////////////////	
		            {
		            "void func1() {"                                                       +"\n"+
		            "    char name[100];"                                                  +"\n"+
		            "    scanf(\"%s\", name);"                                               +"\n"+
		            "	gethostbyaddr(name);"                                                +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2() {"                                                       +"\n"+
		            "    char name[100];"                                                  +"\n"+
		            "    scanf(\"%s\", name);"                                               +"\n"+
		            "	gethostbyname(name);"                                                +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3() {"                                                       +"\n"+
		            "    char name[100];"                                                  +"\n"+
		            "    scanf(\"%s\", name);"                                               +"\n"+
		            "	sethostname(name);"                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "TD"
		            ,
		            },
	/////////////////  10   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int main() {"                                                         +"\n"+
		            "char buf[5012];"                                                      +"\n"+
		            "scanf(\"%s\",buf);"                                                     +"\n"+
		            "printf(buf); "                                                        +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "TD"
		            ,
		            },
	/////////////////  11   ///////////////////	
		            {
		            "void func1() {"                                                       +"\n"+
		            "    int id;"                                                          +"\n"+
		            "    scanf(\"%d\", id);"                                                 +"\n"+
		            "	setpid(id);"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2() {"                                                       +"\n"+
		            "    int id;"                                                          +"\n"+
		            "    scanf(\"%d\", id);"                                                 +"\n"+
		            "	setpgid(1, id);"                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3() {"                                                       +"\n"+
		            "    int pri;"                                                         +"\n"+
		            "    scanf(\"%d\", pri);"                                                +"\n"+
		            "	setpriority(1, 1, pri);"                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "TD"
		            ,
		            },
	/////////////////  12   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <process.h>"                                                 +"\n"+
		            "int main()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "char buf[5];"                                                         +"\n"+
		            "scanf(\"%s\", buf);"                                                    +"\n"+
		            "execl(buf, buf, \"hello\", NULL);"                                      +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "TD"
		            ,
		            },
			 	
				 }	 );
	 }
				 }