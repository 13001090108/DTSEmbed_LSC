package softtest.test.c.gcc.test_team_1;

import static org.junit.Assert.fail;
import static org.junit.Assert.assertEquals;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.apache.log4j.BasicConfigurator;
import org.apache.log4j.PropertyConfigurator;
import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.DefUseAnalysis.c.DUAnalysisVisitor;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.ast.c.ParseException;
import softtest.ast.c.SimpleNode;
import softtest.callgraph.c.CGraph;
import softtest.callgraph.c.CVexNode;
import softtest.cfg.c.ControlFlowData;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.config.c.Config;
import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.CAnalysis;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.fsmanalysis.c.FSMControlFlowData;
import softtest.fsmanalysis.c.Report;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.InterMethodVisitor;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import softtest.summary.lib.c.LibManager;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class NPD_POST extends ModelTestBase {
	public NPD_POST(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD_POST-0.1.xml";
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
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int g_val = 3;"                                                       +"\n"+
		            "int *g_ptr = &g_val;"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "int func1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	func2(1);"                                                           +"\n"+
		            "	return *g_ptr; //DEFECT"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		g_ptr = NULL;"                                                      +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_POST"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int g_val = 3;"                                                       +"\n"+
		            "int *g_ptr = &g_val;"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3();"                                                        +"\n"+
		            "void func4();"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "int func1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	func2(1);"                                                           +"\n"+
		            "	return *g_ptr; //DEFECT"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		g_ptr = NULL;"                                                      +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "	func3();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = &g_val;"                                                     +"\n"+
		            "	func4();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func4()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_POST"
		            ,
		            },
		        	/////////////////  2   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "long g_val = 3;"                                                      +"\n"+
		            "long *g_ptr = &g_val;"                                                +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3();"                                                        +"\n"+
		            "void func4();"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "int func1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	func2(1);"                                                           +"\n"+
		            "	return *g_ptr; //DEFECT"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		g_ptr = NULL;"                                                      +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "	func3();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = &g_val;"                                                     +"\n"+
		            "	func4();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func4()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_POST"
		            ,
		            },
		        	/////////////////  3   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int g_val = 3;"                                                       +"\n"+
		            "int *g_ptr = &g_val;"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "int func1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	*g_ptr = 2; //FP"                                                    +"\n"+
		            "	func2(1);"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		g_ptr = NULL;"                                                      +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int g_val = 3;"                                                       +"\n"+
		            "int *g_ptr = &g_val;"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3();"                                                        +"\n"+
		            "void func4();"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "int func1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	*g_ptr = 2; //FP"                                                    +"\n"+
		            "	func2(1);"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		g_ptr = NULL;"                                                      +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "	func3();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = &g_val;"                                                     +"\n"+
		            "	func4();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func4()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  5   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "long g_val = 3;"                                                      +"\n"+
		            "long *g_ptr = &g_val;"                                                +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3();"                                                        +"\n"+
		            "void func4();"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "int func1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	*g_ptr = 2; //FP"                                                    +"\n"+
		            "	func2(1);"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		g_ptr = NULL;"                                                      +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "	func3();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = &g_val;"                                                     +"\n"+
		            "	func4();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func4()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = 0;"                                                          +"\n"+
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
