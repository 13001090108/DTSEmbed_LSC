package softtest.test.c.gcc.regression_cpp;

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
public class RL extends ModelTestBase {
	public RL(String source,String compiletype, String result)
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
				//////////////////////////0//////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
					"int func1 ()"                                                         +"\n"+
					"{"                                                                    +"\n"+
					"  int * File;"                                                        +"\n"+
					"  FILE * pFile;"                                                      +"\n"+
					"  pFile = fopen (\"myfile.txt\",\"w\");"                              +"\n"+
					"  if (pFile!=NULL)"                                                   +"\n"+
					"  {"                                                                  +"\n"+
					"    fputs (\"fopen example\",pFile);"                                 +"\n"+
					"    fclose (pFile);"                                                  +"\n"+
					"  }"                                                                  +"\n"+
					"  return 0;//FP, RL"                                                  +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////1//////////////////////////////////////////////				            
				{ 
					"#include <stdio.h>"                                                   +"\n"+
					"int func2 ()"                                                         +"\n"+
					"{"                                                                    +"\n"+
					"  FILE * pFile;"                                                      +"\n"+
					"  pFile = fopen (\"myfile.txt\",\"w\");"                              +"\n"+
					"  fputs(\"fopen example\",pFile);"                                    +"\n"+
					"  fclose(pFile);"                                                     +"\n"+
					"  return 0;//FP, RL"                                                  +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////2//////////////////////////////////////////////				            
				{ 
					"#include <stdio.h>"                                                   +"\n"+
					"int func3 ()"                                                         +"\n"+
					"{"                                                                    +"\n"+
					"  FILE * pFile;"                                                      +"\n"+
					"  pFile = fopen (\"myfile.txt\",\"w\");"                              +"\n"+
					"  fputs(\"fopen example\",pFile);"                                    +"\n"+
					"  return 0;//DEFECT, RL, pFile"                                       +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////3//////////////////////////////////////////////				            
				{ 
					"#include <stdio.h>"                                                   +"\n"+
					"FILE * gFile;"                                                        +"\n"+
					"int func4 ()"                                                         +"\n"+
					"{"                                                                    +"\n"+
					"  FILE * pFile;"                                                      +"\n"+
					"  pFile = fopen (\"myfile.txt\",\"w\");"                              +"\n"+
					"  if (pFile==NULL) {"                                                 +"\n"+
					"  	return 0;"                                                         +"\n"+
					"  }"                                                                  +"\n"+
					"  fputs (\"fopen example\",pFile);"                                   +"\n"+
					"  gFile = pFile;"                                                     +"\n"+
					"  return 0;//FP, RL"                                                  +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////4//////////////////////////////////////////////				            
				{
					"#include <stdio.h>"                                                   +"\n"+
					"int func5()"                                                          +"\n"+
					"{"                                                                    +"\n"+
					"  FILE * pFile;"                                                      +"\n"+
					"  pFile = fopen (\"myfile.txt\",\"w\");"                              +"\n"+
					"  if (pFile==NULL) {"                                                 +"\n"+
					"  	return 0;"                                                         +"\n"+
					"  }"                                                                  +"\n"+
					"  fputs (\"fopen example\",pFile);"                                   +"\n"+
					"  fclose(pFile);"                                                     +"\n"+
					"  return 0;//FP, RL"                                                  +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////5//////////////////////////////////////////////				            
				{  
					"#include <stdio.h>"                                                   +"\n"+
					"int func6()"                                                          +"\n"+
					"{"                                                                    +"\n"+
					"  FILE * pFile;"                                                      +"\n"+
					"  pFile = fopen (\"myfile.txt\",\"w\");"                              +"\n"+
					"  if (pFile==NULL) {"                                                 +"\n"+
					"  	return 0;"                                                         +"\n"+
					"  }"                                                                  +"\n"+
					"  fputs (\"fopen example\",pFile);"                                   +"\n"+
					"  return 0;//DEFECT, RL, pFile"                                       +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////6//////////////////////////////////////////////				            
				{ 
					"#include <stdio.h>"                                                   +"\n"+
					"int func7 ()"                                                         +"\n"+
					"{"                                                                    +"\n"+
					"  FILE * pFile;"                                                      +"\n"+
					"  pFile = fopen (\"myfile.txt\",\"w\");"                              +"\n"+
					"  if (pFile!=NULL)"                                                   +"\n"+
					"  {"                                                                  +"\n"+
					"    fputs (\"fopen example\",pFile);"                                 +"\n"+
					"  }"                                                                  +"\n"+
					"  return 0;//DEFECT, RL, pFile"                                       +"\n"+
					"}"      
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////7//////////////////////////////////////////////				            
				{ 
					"#include <stdio.h>"                                                   +"\n"+
					"int func8()"                                                          +"\n"+
					"{"                                                                    +"\n"+
					"  FILE * pFile;"                                                      +"\n"+
					"  pFile = fopen (\"myfile.txt\",\"w\");"                              +"\n"+
					"  if (pFile==NULL) {"                                                 +"\n"+
					"  	int a = 1;"                                                        +"\n"+
					"  	a++;"                                                              +"\n"+
					"  	return 0;"                                                         +"\n"+
					"  }"                                                                  +"\n"+
					"  fputs (\"fopen example\",pFile);"                                   +"\n"+
					"  fclose(pFile);"                                                     +"\n"+
					"  return 0;//FP, FL"                                                  +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////8//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+  
					""                                                                     +"\n"+
					"int func1 (int s)"                                                    +"\n"+
					"{"                                                                    +"\n"+
					"  int  new_sock = socket(s, NULL, NULL); "                            +"\n"+
					"  //do_something(new_sock); "                                         +"\n"+
					"  close(new_sock); "                                                  +"\n"+
					"  return 0;//FP, RL"                                                  +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////9//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					"int func2(int s)"                                                     +"\n"+
					"{"                                                                    +"\n"+
					"  int new_sock = socket(s, NULL, NULL); "                             +"\n"+
					" // do_something(new_sock); "                                         +"\n"+
					"  //closesocket(new_sock);  RL"                                       +"\n"+
					"  return 0;//DEFECT, RL, new_sock"                                    +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////10//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					"int func3 (int portnum)"                                              +"\n"+
					"{"                                                                    +"\n"+
					"  int s; "                                                            +"\n"+
					"  struct sockaddr_in sa; "                                            +"\n"+
					"  struct hostent *hp;"                                                +"\n"+
					"  memset(&sa, 0, sizeof(struct sockaddr_in)); "                       +"\n"+
					"  gethostname(myname, sizeof(myname)); "                              +"\n"+
					"  hp = gethostbyname(myname);"                                        +"\n"+
					"  if (hp == NULL) "                                                   +"\n"+
					"  	return(-1); "                                             +"\n"+
					"  sa.sin_family = hp->h_addrtype; "                                   +"\n"+
					"  sa.sin_port = htons(portnum); "                                     +"\n"+
					"  s = socket(AF_INET, SOCK_STREAM, 0);"                               +"\n"+
					"  if (s == -1) "                                             +"\n"+
					"  	return -1;"                                               +"\n"+
					"  if (bind(s, (struct sockaddr *)&sa, sizeof(struct sockaddr_in)) == int_ERROR) { "+"\n"+
					"  	close(s); "                                                        +"\n"+
					"  	return(-1); "                                             +"\n"+
					"  } "                                                                 +"\n"+
					"  close(s);"                                                          +"\n"+
					"  return 1;//FP, RL"                                                  +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////11//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					"int func4 (int portnum)"                                              +"\n"+
					"{"                                                                    +"\n"+
					"  int s; "                                                            +"\n"+
					"  struct sockaddr_in sa; "                                            +"\n"+
					"  struct hostent *hp;"                                                +"\n"+
					"  memset(&sa, 0, sizeof(struct sockaddr_in)); "                       +"\n"+
					"  gethostname(myname, sizeof(myname)); "                              +"\n"+
					"  hp = gethostbyname(myname);"                                        +"\n"+
					"  if (hp == NULL) "                                                   +"\n"+
					"  	return(-1); "                                             +"\n"+
					"  sa.sin_family = hp->h_addrtype; "                                   +"\n"+
					"  sa.sin_port = htons(portnum); "                                     +"\n"+
					"  s = socket(AF_INET, SOCK_STREAM, 0);"                               +"\n"+
					"  if (s == -1) "                                             +"\n"+
					"  	return -1;"                                               +"\n"+
					"  if (bind(s, (struct sockaddr *)&sa, sizeof(struct sockaddr_in)) == int_ERROR) { "+"\n"+
					"  	close(s); "                                                        +"\n"+
					"  	return(-1); "                                             +"\n"+
					"  } "                                                                 +"\n"+
					"  //close(s); "                                                       +"\n"+
					"  return 1;//DEFECT, RL, s"                                           +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////12//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					"int func4 (int portnum)"                                              +"\n"+
					"{"                                                                    +"\n"+
					"  int s; "                                                            +"\n"+
					"  struct sockaddr_in sa; "                                            +"\n"+
					"  struct hostent *hp;"                                                +"\n"+
					"  memset(&sa, 0, sizeof(struct sockaddr_in)); "                       +"\n"+
					"  gethostname(myname, sizeof(myname)); "                              +"\n"+
					"  hp = gethostbyname(myname);"                                        +"\n"+
					"  if (hp == NULL) "                                                   +"\n"+
					"  	return(-1); "                                             +"\n"+
					"  sa.sin_family = hp->h_addrtype; "                                   +"\n"+
					"  sa.sin_port = htons(portnum); "                                     +"\n"+
					"  s = socket(AF_INET, SOCK_STREAM, 0);"                               +"\n"+
					"  if (s == -1) {"                                            +"\n"+
					"  	int a = 1;"                                                        +"\n"+
					"  	a ++;"                                                             +"\n"+
					"  	return -1;"                                               +"\n"+
					"  }"                                                                  +"\n"+
					"  if (bind(s, (struct sockaddr *)&sa, sizeof(struct sockaddr_in)) == int_ERROR) { "+"\n"+
					"  	close(s); "                                                        +"\n"+
					"  	return(-1); "                                             +"\n"+
					"  } "                                                                 +"\n"+
					"  close(s);"                                                          +"\n"+
					"  return 1;//FP, RL"                                                  +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////13//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					"int func5 (int portnum)"                                              +"\n"+
					"{"                                                                    +"\n"+
					"  int s; "                                                            +"\n"+
					"  struct sockaddr_in sa; "                                            +"\n"+
					"  struct hostent *hp;"                                                +"\n"+
					"  memset(&sa, 0, sizeof(struct sockaddr_in)); "                       +"\n"+
					"  gethostname(myname, sizeof(myname)); "                              +"\n"+
					"  hp = gethostbyname(myname);"                                        +"\n"+
					"  if (hp == NULL) "                                                   +"\n"+
					"  	return(-1); "                                             +"\n"+
					"  sa.sin_family = hp->h_addrtype; "                                   +"\n"+
					"  sa.sin_port = htons(portnum); "                                     +"\n"+
					"  s = socket(AF_INET, SOCK_STREAM, 0);"                               +"\n"+
					"  if (s != -1) {"                                            +"\n"+
					"	  if (bind(s, (struct sockaddr *)&sa, sizeof(struct sockaddr_in)) == int_ERROR) { "+"\n"+
					"	  	close(s); "                                                    +"\n"+
					"	  	return(-1); "                                         +"\n"+
					"	  } "                                                              +"\n"+
					"	  close(s);"                                                       +"\n"+
					"	}"                                                                 +"\n"+
					"  return 1;//FP, RL"                                                  +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////14//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					"int func6 (int portnum)"                                              +"\n"+
					"{"                                                                    +"\n"+
					"  int s; "                                                            +"\n"+
					"  struct sockaddr_in sa; "                                            +"\n"+
					"  struct hostent *hp;"                                                +"\n"+
					"  memset(&sa, 0, sizeof(struct sockaddr_in)); "                       +"\n"+
					"  gethostname(myname, sizeof(myname)); "                              +"\n"+
					"  hp = gethostbyname(myname);"                                        +"\n"+
					"  sa.sin_family = hp->h_addrtype; "                                   +"\n"+
					"  sa.sin_port = htons(portnum); "                                     +"\n"+
					"  s = socket(AF_INET, SOCK_STREAM, 0);"                               +"\n"+
					"  if (s != -1) {"                                            +"\n"+
					"	  if (bind(s, (struct sockaddr *)&sa, sizeof(struct sockaddr_in)) == int_ERROR) { "+"\n"+
					"	  	close(s); "                                                    +"\n"+
					"	  	return(-1); "                                         +"\n"+
					"	  } "                                                              +"\n"+
					"	}"                                                                 +"\n"+
					"  return 1;//DEFECT, RL, s"                                           +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////15//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					"int func7 (int portnum)"                                              +"\n"+
					"{"                                                                    +"\n"+
					"  int s; "                                                            +"\n"+
					"  struct sockaddr_in sa; "                                            +"\n"+
					"  struct hostent *hp;"                                                +"\n"+
					"  memset(&sa, 0, sizeof(struct sockaddr_in)); "                       +"\n"+
					"  gethostname(myname, sizeof(myname)); "                              +"\n"+
					"  hp = gethostbyname(myname);"                                        +"\n"+
					"  sa.sin_family = hp->h_addrtype; "                                   +"\n"+
					"  sa.sin_port = htons(portnum); "                                     +"\n"+
					"  s = socket(AF_INET, SOCK_STREAM, 0);"                               +"\n"+
					"  if (s != -1) {"                                            +"\n"+
					"	  if (bind(s, (struct sockaddr *)&sa, sizeof(struct sockaddr_in)) == int_ERROR) { "+"\n"+
					"	  	close(s); "                                                    +"\n"+
					"	  	return(-1); "                                         +"\n"+
					"	  } else {"                                                        +"\n"+
					"	  	int a = 1;"                                                    +"\n"+
					"	  	a = 1;"                                                        +"\n"+
					"	 	} "                                                            +"\n"+
					"	}"                                                                 +"\n"+
					"  return 1;//DEFECT, RL, s"                                           +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////16//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					"int func8 (int portnum)"                                              +"\n"+
					"{"                                                                    +"\n"+
					"  int s; "                                                            +"\n"+
					"  struct sockaddr_in sa; "                                            +"\n"+
					"  struct hostent *hp;"                                                +"\n"+
					"  memset(&sa, 0, sizeof(struct sockaddr_in)); "                       +"\n"+
					"  gethostname(myname, sizeof(myname)); "                              +"\n"+
					"  hp = gethostbyname(myname);"                                        +"\n"+
					"  sa.sin_family = hp->h_addrtype; "                                   +"\n"+
					"  sa.sin_port = htons(portnum); "                                     +"\n"+
					"  s = socket(AF_INET, SOCK_STREAM, 0);"                               +"\n"+
					"  if (s != -1) {"                                            +"\n"+
					"	  if (bind(s, (struct sockaddr *)&sa, sizeof(struct sockaddr_in)) == int_ERROR) { "+"\n"+
					"	  	close(s); "                                                    +"\n"+
					"	  	return(-1); "                                         +"\n"+
					"	  } else {"                                                        +"\n"+
					"	  	int a = 1;"                                                    +"\n"+
					"	  	a = 1;"                                                        +"\n"+
					"	  	close(s); "                                                    +"\n"+
					"	 	} "                                                            +"\n"+
					"	}"                                                                 +"\n"+
					"  return 1;//FP, RL"                                                  +"\n"+
					"}"                                                                   
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////17//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					"int func9 (int portnum)"                                              +"\n"+
					"{"                                                                    +"\n"+
					"  int s; "                                                            +"\n"+
					"  struct sockaddr_in sa; "                                            +"\n"+
					"  struct hostent *hp;"                                                +"\n"+
					"  s = socket(AF_INET, SOCK_STREAM, 0);"                               +"\n"+
					"  if (s == -1) {"                                            +"\n"+
					"  	int a = 1;"                                                        +"\n"+
					"  	a ++;"                                                             +"\n"+
					"  	return -1;"                                               +"\n"+
					"  } else {"                                                           +"\n"+
					"	  if (bind(s, (struct sockaddr *)&sa, sizeof(struct sockaddr_in)) == int_ERROR) { "+"\n"+
					"	  	close(s); "                                                    +"\n"+
					"	  	return(-1); "                                         +"\n"+
					"	  } "                                                              +"\n"+
					"	  close(s);"                                                       +"\n"+
					"	}"                                                                 +"\n"+
					"  return 1;//FP, RL"                                                  +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////18//////////////////////////////////////////////
				{
					"#include<stdio.h>"                                                    +"\n"+
					"int stat_retry (char *file);"                                         +"\n"+
					"int feat_s2mfc_read(char *file)"                                      +"\n"+
					"{"                                                                    +"\n"+
					"    FILE *fp;"                                                        +"\n"+
					"    if ((stat_retry(file) < 0)"                                       +"\n"+
					"        || ((fp = fopen(file, \"rb\")) == NULL)) {"                   +"\n"+
					"        return -1;//RL,fp"                                            +"\n"+
					"    }"                                                                +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////19//////////////////////////////////////////////
				/*xwt:在获得*pf的scope的时候为空，没有识别*pf，造成AliasSet处出错，需问zhb。*/
				{
					"  #include <stdio.h>"                                                 +"\n"+
					"  "                                                                   +"\n"+
					"  int my_open_r(const char *name, FILE **pf) {"                       +"\n"+
					"      FILE *f = fopen(name, \"r\");"                                  +"\n"+
					"      if (!f) {"                                                      +"\n"+
					"          return -1;"                                                 +"\n"+
					"      }"                                                              +"\n"+
					"      *pf = f;"                                                       +"\n"+
					"      return 0;"                                                      +"\n"+
					" }"                                                                   +"\n"+
					" "                                                                    +"\n"+
					" int test_file(const char *name) {"                                   +"\n"+
					"     FILE *dummy;"                                                    +"\n"+
					"     if (my_open_r(name, &dummy) == -1) {"                            +"\n"+
					"         fprintf(stderr, \"Problem with: %s\\n\", name);"             +"\n"+
					"         return 0; //DEFECT"                                          +"\n"+
					"     }"                                                               +"\n"+
					"     return 1; //DEFECT"                                              +"\n"+
					" }"                                                                   
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////20//////////////////////////////////////////////	
				{
					"#include<stdio.h>"                                                    +"\n"+
					"int main()"                                                           +"\n"+
					"{"                                                                    +"\n"+
					"    FILE *f;"                                                         +"\n"+
					""                                                                     +"\n"+
					"    f = fopen(\"abc.txt\", \"r\");"                                   +"\n"+
					"    if(f == NULL)"                                                    +"\n"+
					"        return -1;"                                                   +"\n"+
					""                                                                     +"\n"+
					"    fclose(f);"                                                       +"\n"+
					"    return 0;"                                                        +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},

				//////////////////////////21////////////////////////////////////////	
				{
					"#include <stdio.h>"                                                   +"\n"+
					""                                                                     +"\n"+
					"void func(char *var)"                                                 +"\n"+
					"{"                                                                    +"\n"+
					"	FILE *fp;"                                                           +"\n"+
					""                                                                     +"\n"+
					"	if ((fp = fopen(var, \"rw\")) == NULL)"                                +"\n"+
					"		return;  //FP"                                                      +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////22//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                                +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					"int func4 (int portnum)"                                              +"\n"+
					"{"                                                                    +"\n"+
					"  int s; "                                                         +"\n"+
					"  s = socket(AF_INET, SOCK_STREAM, 0);"                               +"\n"+
					"  if (s == -1) "                                          +"\n"+
					"  	return -1;"                                            +"\n"+
					"  if (bind(s, (struct sockaddr *)&s, sizeof(struct sockaddr_in)) == int_ERROR) { "+"\n"+
					"  	close(s); "                                                  +"\n"+
					"  	return(-1); "                                          +"\n"+
					"  } "                                                                 +"\n"+
					"  return 1;//DEFECT, RL, s"                                           +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////23/////////////////////////////////////////////
				/*xwt:没有重复处理机制*/
				{
					"#include<stdio.h>"                                                    +"\n"+
					"FILE *f;"                                                             +"\n"+
					"void fa()"                                                             +"\n"+
					"{"                                                                    +"\n"+
					"    f = fopen(\"abc.txt\", \"r\");"                                       +"\n"+
					"}"                                                                    +"\n"+
					"void f1(){"                                                           +"\n"+
					"    fa();"                                                             +"\n"+
					"    f = fopen(\"abc.txt\", \"r\");"                                       +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"RL"
					,
				},

				//////////////////////////24//////////////////////////////////////////////
				//这种情况可以查，可以报fun1不完全释放。不过是基于close在if下面。
				//我加一个else里面再close照样还是不完全释放，所以我把那个蹩脚的功能先注释了
				{
					"#include <sys/socket.h>"                                                +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					""                                                                     +"\n"+
					"void fun1(int s,int flag){"                                        +"\n"+
					"	if(flag)"                                                            +"\n"+
					"		close(s);"                                                    +"\n"+
					""                                                                     +"\n"+
					"}"                                                                    +"\n"+
					"void fun2(int s){"                                                 +"\n"+
					""                                                                     +"\n"+
					"	close(s);"                                                     +"\n"+
					""                                                                     +"\n"+
					"}"                                                                    +"\n"+
					"void f(int flag){"                                                    +"\n"+
					"	int s1, s2;"                                                      +"\n"+
					""                                                                     +"\n"+
					"	s1 = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);"                     +"\n"+
					"	s2 = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);"                     +"\n"+
					""                                                                     +"\n"+
					"	fun1(s1,flag);"                                                      +"\n"+
					"	fun2(s2);"                                                           +"\n"+
					"	return; //DEFECT"                                                    +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////25//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					""                                                                     +"\n"+
					"void fun2(int s){"                                                    +"\n"+
					""                                                                     +"\n"+
					"	close(s);"                                                         +"\n"+
					""                                                                     +"\n"+
					"}"                                                                    +"\n"+
					"void fun3(int s){"                                                    +"\n"+
					"	fun2(s);"                                                          +"\n"+
					"}"                                                                    +"\n"+
					""                                                                     +"\n"+
					"void f(int flag){"                                                    +"\n"+
					"	int s;"                                                            +"\n"+
					""                                                                     +"\n"+
					"	s = socket();"                                                     +"\n"+
					"	fun3(s);"                                                          +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////26//////////////////////////////////////////////
				{
					//xwt:参数释放和分配功能就没实现
					"#include <stdio.h>"                                                   +"\n"+
					""                                                                     +"\n"+
					"int flag;"                                                            +"\n"+
					"void fun2(FILE *p){"                                                  +"\n"+
					"        if(p)"                                                        +"\n"+
					"		   fclose(p);"                                                      +"\n"+
					""                                                                     +"\n"+
					"}"                                                                    +"\n"+
					""                                                                     +"\n"+
					"void f(char *var){"                                                   +"\n"+
					"	FILE *p = fopen(var, \"r\");"                                          +"\n"+
					"	fun2(p);"                                                            +"\n"+
					""                                                                     +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////27//////////////////////////////////////////////
				{
					//同上
					"#include <stdio.h>"                                                   +"\n"+
					""                                                                     +"\n"+
					"int flag;"                                                            +"\n"+
					"void fun2(FILE *p){"                                                  +"\n"+
					"    fclose(p);"                                                       +"\n"+
					""                                                                     +"\n"+
					"}"                                                                    +"\n"+
					""                                                                     +"\n"+
					"void f(char *var){"                                                   +"\n"+
					"	FILE *p = fopen(var, \"r\");"                                          +"\n"+
					"	fun2(p);"                                                            +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////28//////////////////////////////////////////////	
				{
					"#include <sys/socket.h>"                                                +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					""                                                                     +"\n"+
					"void func2(int);"                                                  +"\n"+
					""                                                                     +"\n"+
					"void func1()"                                                         +"\n"+
					"{"                                                                    +"\n"+
					"	int sckt;"                                                        +"\n"+
					""                                                                     +"\n"+
					"	sckt = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);"                   +"\n"+
					"	func2(sckt);"                                                        +"\n"+
					"	return; //FP"                                                        +"\n"+
					"}"                                                                    +"\n"+
					""                                                                     +"\n"+
					"void func2(int var)"                                               +"\n"+
					"{"                                                                    +"\n"+
					"	close(var);"                                                   +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},

				//////////////////////////29//////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                                +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					""                                                                     +"\n"+
					"void func2(int, int, int);"                                        +"\n"+
					""                                                                     +"\n"+
					"void func1(int var)"                                               +"\n"+
					"{"                                                                    +"\n"+
					"	int sckt;"                                                        +"\n"+
					""                                                                     +"\n"+
					"	sckt = accept(var, NULL, NULL);"                                     +"\n"+
					"	func2(0, 0, sckt);"                                                  +"\n"+
					"	return; //FP"                                                        +"\n"+
					"}"                                                                    +"\n"+
					""                                                                     +"\n"+
					"void func2(int n, int m, int var)"                                 +"\n"+
					"{"                                                                    +"\n"+
					"	close(var);"                                                   +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},


				//////////////////////////30//////////////////////////////////////////////
				/*xwt:加函数摘要的时候无法提取变量信息variable，tmp类型为CPPType_unknow，加摘要失败
				 * 我觉得原因应该是不识别int类型。
				 * 另，这又涉及到Variable和VariableNameDeclaration这两个概念，后者是能正常识别的，
				 * 而过程内状态机只用到后者，这就是过程内 不会出现误报的原因。
				 * 而在正常情况下后者应该包含前者。目前的情况就是后者里面的Variable信息为null*/
				//jdh 需要修改 xwt
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					""                                                                     +"\n"+
					"int func2();"                                                         +"\n"+
					""                                                                     +"\n"+
					"void func1()"                                                         +"\n"+
					"{"                                                                    +"\n"+
					"	int tmp;"                                                          +"\n"+
					""                                                                     +"\n"+
					"	tmp = func2();"                                                    +"\n"+
					"	return; //DEFECT"                                                  +"\n"+
					"}"                                                                    +"\n"+
					""                                                                     +"\n"+
					"int func2()"                                                          +"\n"+
					"{"                                                                    +"\n"+
					"	int sckt;"                                                         +"\n"+
					""                                                                     +"\n"+
					"	sckt = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);"                 +"\n"+
					"	return sckt;"                                                      +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"RL"
					,
				},

				//////////////////////////31//////////////////////////////////////////////
				/*xwt:问题同37，当遇到过程间需要摘要约束时且相关变量为FILE或int的时候，
				 * 无法获得变量信息*/
				//jdh  需要修改 xwt
				{
					"#include <stdio.h>"                                                   +"\n"+
					""                                                                     +"\n"+
					"FILE* func2();"                                                       +"\n"+
					""                                                                     +"\n"+
					"void func1()"                                                         +"\n"+
					"{"                                                                    +"\n"+
					"	FILE *fp;"                                                           +"\n"+
					""                                                                     +"\n"+
					"	fp = func2();"                                                       +"\n"+
					"	fputs(\"sample\", fp);"                                                +"\n"+
					"	return; //DEFECT"                                                    +"\n"+
					"}"                                                                    +"\n"+
					""                                                                     +"\n"+
					"FILE* func2()"                                                        +"\n"+
					"{"                                                                    +"\n"+
					"	FILE *fp;"                                                           +"\n"+
					""                                                                     +"\n"+
					"	fp = fopen(\"test.txt\", \"w\");"                                        +"\n"+
					"	return fp;"                                                          +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////32//////////////////////////////////////////////
				{
					"  #include <stdio.h>"                                                 +"\n"+
					"  "                                                                   +"\n"+
					"  FILE * my_open_r(const char *name) {"                               +"\n"+
					"      FILE *pf = fopen(name, \"r\");"                                  +"\n"+
					"      return pf;"                                                      +"\n"+
					" }"                                                                   +"\n"+
					" "                                                                    +"\n"+
					" int test_file(const char *name) {"                                   +"\n"+
					"     FILE *dummy;"                                                    +"\n"+
					"     dummy = my_open_r(name);"                                         +"\n"+
					"     return 1; //DEFECT"                                              +"\n"+
					" }"                                                                   
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////33//////////////////////////////////////////////
				{
					"  #include <stdio.h>"                                                 +"\n"+
					"  "                                                                   +"\n"+
					"  int my_open_r(const char *name, FILE **pf) {"                       +"\n"+
					"      *pf = fopen(name, \"r\");"                                      +"\n"+
					"      if (1) {"                                                      +"\n"+
					"          return -1;"                                                 +"\n"+
					"      }"                                                              +"\n"+
					"      return 0;"                                                      +"\n"+
					" }"                                                                   +"\n"+
					" "                                                                    +"\n"+
					" int test_file(const char *name) {"                                   +"\n"+
					"     FILE *dummy;"                                                    +"\n"+
					"     if (my_open_r(name, &dummy) == -1) {"                            +"\n"+
					"         fprintf(stderr, \"Problem with: %s\\n\", name);"             +"\n"+
					"         return 0; //DEFECT"                                          +"\n"+
					"     }"                                                               +"\n"+
					"     return 1; //DEFECT"                                              +"\n"+
					" }"                                                                   
					,
					"gcc"
					,
					"RL"
					,
				},
				//////////////////////////34//////////////////////////////////////////////
				{
					"  #include <stdio.h>"                                                 +"\n"+
					"  "                                                                   +"\n"+
					"  int my_open_r(const char *name, FILE **pf) {"                       +"\n"+
					"      *pf = fopen(name, \"r\");"                                      +"\n"+
					"      return 0;"                                                      +"\n"+
					" }"                                                                   +"\n"+
					" "                                                                    +"\n"+
					" int test_file(const char *name) {"                                   +"\n"+
					"     FILE *dummy;"                                                    +"\n"+
					"     if (my_open_r(name, &dummy) == -1) {"                            +"\n"+
					"         fprintf(stderr, \"Problem with: %s\\n\", name);"             +"\n"+
					"         return 0; //DEFECT"                                          +"\n"+
					"     }"                                                               +"\n"+
					"     fclose(dummy);"                                                  +"\n"+
					"     return 1; //DEFECT"                                              +"\n"+
					" }"                                                                   
					,
					"gcc"
					,
					"RL"
					,
				},
//////////////////////////34/////////////////////////////////////////////
				{
					"#include <sys/socket.h>"                                              +"\n"+
					"#include <unistd.h>"                                                  +"\n"+ 
					"int func9 (int portnum)"                                              +"\n"+
					"{"                                                                    +"\n"+
					"  int s; "                                                         +"\n"+
					"  s = socket(AF_INET, SOCK_STREAM, 0);"                               +"\n"+
					"  if (s == -1) {"                                         +"\n"+
					"  	int a = 1;"                                                        +"\n"+
					"  	a ++;"                                                             +"\n"+
					"  	return -1;"                                            +"\n"+
					"  } else {"                                                           +"\n"+
					"	  close(s);"                                                 +"\n"+
					"	}"                                                                 +"\n"+
					"  return 1;//FP, RL"                                                  +"\n"+
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