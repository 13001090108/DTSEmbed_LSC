package softtest.test.android.gcc;

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
public class UFM extends ModelTestBase {
	public UFM(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UFM-0.1.xml";
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
		            "static struct input_keychord *keychords = 0;"                         +"\n"+
		            "void keychord_init()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "    int fd, ret;"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "    service_for_each(add_service_keycodes);"                          +"\n"+
		            ""                                                                     +"\n"+
		            "    /* nothing to do if no services require keychords */"             +"\n"+
		            "    if (!keychords)"                                                  +"\n"+
		            "        return;"                                                      +"\n"+
		            ""                                                                     +"\n"+
		            "    fd = open(\"/dev/keychord\", O_RDWR);"                              +"\n"+
		            "    if (fd < 0) {"                                                    +"\n"+
		            "        ERROR(\"could not open /dev/keychord\\n\");"                     +"\n"+
		            "        return;"                                                      +"\n"+
		            "    }"                                                                +"\n"+
		            "    fcntl(fd, F_SETFD, FD_CLOEXEC);"                                  +"\n"+
		            ""                                                                     +"\n"+
		            "    ret = write(fd, keychords, keychords_length);"                    +"\n"+
		            "    if (ret != keychords_length) {"                                   +"\n"+
		            "        ERROR(\"could not configure /dev/keychord %d (%d)\\n\", ret, errno);"+"\n"+
		            "        close(fd);"                                                   +"\n"+
		            "        fd = -1;"                                                     +"\n"+
		            "    }"                                                                +"\n"+
		            ""                                                                     +"\n"+
		            "    free(keychords);"                                                 +"\n"+
		            "    keychords = 0;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "    keychord_fd = fd;"                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
  /////////////////  0   ///////////////////	
                    {
                    "#include<stdio.h>"                                                    +"\n"+
                    "#include<stdlib.h>"                                                   +"\n"+
                    "int main(){"                                                          +"\n"+
                    "   int *table;"                                                       +"\n"+
                    "   //table = (int *)malloc(sizeof(int));"                               +"\n"+
                    "   free (table);  // Wrong defect"                                    +"\n"+
                    "}"                                                                    
                    ,
                    "gcc"
                    ,
                    "OK"
                    ,
                    },
    /////////////////  0   ///////////////////	
                    {
                     "#include<stdlib.h>"                                                   +"\n"+
                    " hnj_free (void *p)"                                                   +"\n"+
                    "{"                                                                    +"\n"+
                    "  free (p);"                                                          +"\n"+
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