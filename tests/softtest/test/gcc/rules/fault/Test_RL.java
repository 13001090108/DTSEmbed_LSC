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
public class Test_RL extends ModelTestBase{
	public Test_RL(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/RL-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/rm_summary.xml";
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
		            "#include<stdio.h>"                                                    +"\n"+
		            "#include<stdlib.h>"                                                   +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE *file;"                                                        +"\n"+
		            "  int i=0;"                                                           +"\n"+
		            "  if((file=fopen(\"C:\\\\temp\",\"r\"))==NULL)"                             +"\n"+
		            "     return;"                                                         +"\n"+
		            "  int n=5;  "                                                         +"\n"+
		            "  while(n--)"                                                         +"\n"+
		            "  {"                                                                  +"\n"+
		            "	if(!i)"                                                              +"\n"+
		            "      return;"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "  }"                                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RL"
		            ,
		            },
        ///////////////  0   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int func1 ()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  pFile = fopen (\"myfile.txt\",\"w\");"                                  +"\n"+
		            "  if (pFile!=NULL)"                                                   +"\n"+
		            "  {"                                                                  +"\n"+
		            "    fputs (\"fopen example\",pFile);"                                   +"\n"+
		            "    fclose (pFile);"                                                  +"\n"+
		            "  }"                                                                  +"\n"+
		            "  return 0;"                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int func2 ()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  pFile = fopen (\"myfile.txt\",\"w\");"                                  +"\n"+
		            "  fputs(\"fopen example\",pFile);"                                      +"\n"+
		            "  fclose(pFile);"                                                     +"\n"+
		            "  return 0;//FP, RL"                                                  +"\n"+
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
		            "int func3 ()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  pFile = fopen (\"myfile.txt\",\"w\");"                                  +"\n"+
		            "  fputs(\"fopen example\",pFile);"                                      +"\n"+
		            "  return 0;//DEFECT, RL, pFile"                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RL"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "FILE * gFile;"                                                        +"\n"+
		            "int func4 ()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  pFile = fopen (\"myfile.txt\",\"w\");"                                  +"\n"+
		            "  if (pFile==NULL) {"                                                 +"\n"+
		            "  	return 0;"                                                         +"\n"+
		            "  }"                                                                  +"\n"+
		            "  fputs (\"fopen example\",pFile);"                                     +"\n"+
		            "  gFile = pFile;"                                                     +"\n"+
		            "  return 0;//FP, RL"                                                  +"\n"+
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
		            "int func5()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  pFile = fopen (\"myfile.txt\",\"w\");"                                  +"\n"+
		            "  if (pFile==NULL) {"                                                 +"\n"+
		            "  	return 0;"                                                         +"\n"+
		            "  }"                                                                  +"\n"+
		            "  fputs (\"fopen example\",pFile);"                                     +"\n"+
		            "  fclose(pFile);"                                                     +"\n"+
		            "  return 0;//FP, RL"                                                  +"\n"+
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
		            "int func6()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  pFile = fopen (\"myfile.txt\",\"w\");"                                  +"\n"+
		            "  if (pFile==NULL) {"                                                 +"\n"+
		            "  	return 0;"                                                         +"\n"+
		            "  }"                                                                  +"\n"+
		            "  fputs (\"fopen example\",pFile);"                                     +"\n"+
		            "  return 0;//DEFECT, RL, pFile"                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RL"
		            ,
		            },
	/////////////////  6   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int func7 ()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  pFile = fopen (\"myfile.txt\",\"w\");"                                  +"\n"+
		            "  if (pFile!=NULL)"                                                   +"\n"+
		            "  {"                                                                  +"\n"+
		            "    fputs (\"fopen example\",pFile);"                                   +"\n"+
		            "  }"                                                                  +"\n"+
		            "  return 0;//DEFECT, RL, pFile"                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RL"
		            ,
		            },
	/////////////////  7   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int func8()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  pFile = fopen (\"myfile.txt\",\"w\");"                                  +"\n"+
		            "  if (pFile==NULL) {"                                                 +"\n"+
		            "  	int a = 1;"                                                        +"\n"+
		            "  	a++;"                                                              +"\n"+
		            "  	return 0;"                                                         +"\n"+
		            "  }"                                                                  +"\n"+
		            "  fputs (\"fopen example\",pFile);"                                     +"\n"+
		            "  fclose(pFile);"                                                     +"\n"+
		            "  return 0;//FP, FL"                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  8   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "FILE * gFile;"                                                        +"\n"+
		            
		            "int ff (){"                                                        +"\n"+
		            "	 gFile = fopen (\"myfile_1.txt\",\"w\");"                                +"\n"+
		            "	}"                                                                      +"\n"+  
		            "int func9 ()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  pFile = fopen (\"myfile.txt\",\"w\");"                                  +"\n"+
		            "  if (pFile==NULL) {"                                                 +"\n"+
		            "  	return 0;"                                                         +"\n"+
		            "  }"                                                                  +"\n"+
		            "  fputs (\"fopen example\",pFile);"                                     +"\n"+
		            "  gFile = pFile;"                                                     +"\n"+
		            "  ff ();"                                                          +"\n"+
		            "  return 0;//FP, RL"                                                  +"\n"+
		            "}"  //                                                                  +"\n"+
		                                                                   
		            ,
		            "gcc"
		            ,
		            "OK"
		            },
	/////////////////  9   ///////////////////	
		            {
		            "#include <stdio.h>"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "FILE *"                                                               +"\n"+
		            "file_open (char *file_name, int write_flag)"                          +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE *fp;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "  return fp;"                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		            
	/////////////////  10   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "#include <stdio.h>"                                                 +"\n"+
		            "int"                                                                  +"\n"+
		            "open_index_file (filename, streams, new)"                             +"\n"+
		            "     char *filename;"                                                 +"\n"+
		            "     FILE **streams;"                                                 +"\n"+
		            "     int new;"                                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *index_base_file_name;"                                        +"\n"+
		            "  char *index_record_file_name;"                                      +"\n"+
		            "  int return_code;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "  streams[0] = fopen (index_base_file_name, \"a+\");"                   +"\n"+
		            "  if (streams[0] == NULL) {"                                          +"\n"+
		            "    perror (index_base_file_name);"                                   +"\n"+
		            "    return EXIT_FAILURE;"                                             +"\n"+
		            "    }"                                                                +"\n"+
		            ""                                                                     +"\n"+
		            "  return 0;"                                               +"\n"+
		            "  }"                                                                  
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		            
	/////////////////  11   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "#include <stdio.h>"                                                 +"\n"+
		            "int"                                                                  +"\n"+
		            "open_index_file (char *filename, FILE **streams, int new)"                             +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *index_base_file_name;"                                        +"\n"+
		            "  char *index_record_file_name;"                                      +"\n"+
		            "  int return_code;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "  streams[0] = fopen (index_base_file_name, \"a+\");"                   +"\n"+
		            "  if (streams[0] == NULL) {"                                          +"\n"+
		            "    perror (index_base_file_name);"                                   +"\n"+
		            "    return EXIT_FAILURE;"                                             +"\n"+
		            "    }"                                                                +"\n"+
		            ""                                                                     +"\n"+
		            "  return 0;"                                               +"\n"+
		            "  }"                                                                  
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },


		            

		 });
	 }
}
