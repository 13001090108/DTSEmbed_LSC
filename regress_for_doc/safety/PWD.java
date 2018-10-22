package safety;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;

import org.junit.BeforeClass;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.fsmanalysis.c.Report;
import softtest.interpro.c.InterContext;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class PWD extends ModelTestBase
{
	public PWD(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/safety/PWD-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("safety");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
	}
	@Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(
				 new Object[][]
				 {
			/////////////////  1   ///////////////////	
				            {
				            "#include <stdlib.h>  "                                                +"\n"+
				            "#include <stdio.h>  "                                                 +"\n"+
				            "#include <mysql.h>  "                                                 +"\n"+
				            "  "                                                                   +"\n"+
				            "int main(int argc, char *argv[])  "                                   +"\n"+
				            "{  "                                                                  +"\n"+
				            "    int res;  "                                                       +"\n"+
				            "    MYSQL connection;  "                                              +"\n"+
				            "  "                                                                   +"\n"+
				            "    mysql_init(&connection);  "                                       +"\n"+
				            "    if(mysql_real_connect(&connection, \"localhost\", \"root\", \"pwd\", \"test\", 0, NULL, 0))  "+"\n"+
				            "    {  "                                                              +"\n"+
				            "        printf(\"Connection success\\n\");  "                            +"\n"+
				            "  "                                                                   +"\n"+
				            "        res = mysql_query(&connection, \"INSERT INTO children(fname, age) VALUES('ann', 3)\");  "+"\n"+
				            "  "                                                                   +"\n"+
				            "        if(!res)  "                                                   +"\n"+
				            "        {  "                                                          +"\n"+
				            "            printf(\"Inserted %lu rows\\n\", (unsigned long)mysql_affected_rows(&connection)); //打印受影响的行数  "+"\n"+
				            "        }  "                                                          +"\n"+
				            "        else  "                                                       +"\n"+
				            "        {  "                                                          +"\n"+
				            "            fprintf(stderr, \"Insert error %d: %s\\n\", mysql_errno(&connection), mysql_error(&connection));  "+"\n"+
				            "        }  "                                                          +"\n"+
				            "  "                                                                   +"\n"+
				            "        mysql_close(&connection);  "                                  +"\n"+
				            "    }  "                                                              +"\n"+
				            "    else  "                                                           +"\n"+
				            "    {  "                                                              +"\n"+
				            "        fprintf(stderr, \"Connection failed\\n\");  "                    +"\n"+
				            "        if(mysql_errno(&connection))  "                               +"\n"+
				            "        {  "                                                          +"\n"+
				            "            fprintf(stderr, \"Connection error %d: %s\\n\", mysql_errno(&connection), mysql_error(&connection));  "+"\n"+
				            "        }  "                                                          +"\n"+
				            "    }  "                                                              +"\n"+
				            "  "                                                                   +"\n"+
				            "    return EXIT_SUCCESS;  "                                           +"\n"+
				            "}  "                                                                  
			                ,
				            "gcc"
				            ,
				            "PWD"
				            ,
			                },
			/////////////////  2   ///////////////////	
			                {
			                "#include <stdlib.h>  "                                                +"\n"+
			                "#include <stdio.h>  "                                                 +"\n"+
			                "#include <mysql.h>  "                                                 +"\n"+
			                "  "                                                                   +"\n"+
			                "int main(int argc, char *argv[])  "                                   +"\n"+
			                "{  "                                                                  +"\n"+
			                "    int res;  "                                                       +"\n"+
			                "    MYSQL connection;  "                                              +"\n"+
			                "  	 char* pwd = \"pwd\";"                                               +"\n"+
			                "    mysql_init(&connection);  "                                       +"\n"+
			                "    if(mysql_real_connect(&connection, \"localhost\", \"root\", pwd, \"test\", 0, NULL, 0))  "+"\n"+
			                "    {  "                                                              +"\n"+
			                "        printf(\"Connection success\\n\");  "                            +"\n"+
			                "  "                                                                   +"\n"+
			                "        res = mysql_query(&connection, \"INSERT INTO children(fname, age) VALUES('ann', 3)\");  "+"\n"+
			                "  "                                                                   +"\n"+
			                "        if(!res)  "                                                   +"\n"+
			                "        {  "                                                          +"\n"+
			                "            printf(\"Inserted %lu rows\\n\", (unsigned long)mysql_affected_rows(&connection)); //打印受影响的行数  "+"\n"+
			                "        }  "                                                          +"\n"+
			                "        else  "                                                       +"\n"+
			                "        {  "                                                          +"\n"+
			                "            fprintf(stderr, \"Insert error %d: %s\\n\", mysql_errno(&connection), mysql_error(&connection));  "+"\n"+
			                "        }  "                                                          +"\n"+
			                "  "                                                                   +"\n"+
			                "        mysql_close(&connection);  "                                  +"\n"+
			                "    }  "                                                              +"\n"+
			                "    else  "                                                           +"\n"+
			                "    {  "                                                              +"\n"+
			                "        fprintf(stderr, \"Connection failed\\n\");  "                    +"\n"+
			                "        if(mysql_errno(&connection))  "                               +"\n"+
			                "        {  "                                                          +"\n"+
			                "            fprintf(stderr, \"Connection error %d: %s\\n\", mysql_errno(&connection), mysql_error(&connection));  "+"\n"+
			                "        }  "                                                          +"\n"+
			                "    }  "                                                              +"\n"+
			                "  "                                                                   +"\n"+
			                "    return EXIT_SUCCESS;  "                                           +"\n"+
			                "}  "                                                                  
			                ,
				            "gcc"
				            ,
				            "PWD"
				            ,
			                },
			/////////////////  3   ///////////////////	
			                {
			                "#include <stdlib.h>  "                                                +"\n"+
			                "#include <stdio.h>  "                                                 +"\n"+
			                "#include <mysql.h>  "                                                 +"\n"+
			                "  "                                                                   +"\n"+
			                "int main(int argc, char *argv[])  "                                   +"\n"+
			                "{  "                                                                  +"\n"+
			                "    int res;  "                                                       +"\n"+
			                "    MYSQL connection;  "                                              +"\n"+
			                "  	"                                                                  +"\n"+
			                "    mysql_init(&connection);  "                                       +"\n"+
			                "    if(mysql_real_connect(&connection, \"localhost\", \"root\", NULL, \"test\", 0, NULL, 0))  "+"\n"+
			                "    {  "                                                              +"\n"+
			                "        printf(\"Connection success\\n\");  "                            +"\n"+
			                "  "                                                                   +"\n"+
			                "        res = mysql_query(&connection, \"INSERT INTO children(fname, age) VALUES('ann', 3)\");  "+"\n"+
			                "  "                                                                   +"\n"+
			                "        if(!res)  "                                                   +"\n"+
			                "        {  "                                                          +"\n"+
			                "            printf(\"Inserted %lu rows\\n\", (unsigned long)mysql_affected_rows(&connection)); //打印受影响的行数  "+"\n"+
			                "        }  "                                                          +"\n"+
			                "        else  "                                                       +"\n"+
			                "        {  "                                                          +"\n"+
			                "            fprintf(stderr, \"Insert error %d: %s\\n\", mysql_errno(&connection), mysql_error(&connection));  "+"\n"+
			                "        }  "                                                          +"\n"+
			                "  "                                                                   +"\n"+
			                "        mysql_close(&connection);  "                                  +"\n"+
			                "    }  "                                                              +"\n"+
			                "    else  "                                                           +"\n"+
			                "    {  "                                                              +"\n"+
			                "        fprintf(stderr, \"Connection failed\\n\");  "                    +"\n"+
			                "        if(mysql_errno(&connection))  "                               +"\n"+
			                "        {  "                                                          +"\n"+
			                "            fprintf(stderr, \"Connection error %d: %s\\n\", mysql_errno(&connection), mysql_error(&connection));  "+"\n"+
			                "        }  "                                                          +"\n"+
			                "    }  "                                                              +"\n"+
			                "  "                                                                   +"\n"+
			                "    return EXIT_SUCCESS;  "                                           +"\n"+
			                "}  "                                                                  
			                ,
				            "gcc"
				            ,
				            "PWD"
				            ,
			                },
			/////////////////  4   ///////////////////	
			                {
			                "#include<grp.h>"                                                      +"\n"+
			                "#include<sys/types.h>"                                                +"\n"+
			                "main()"                                                               +"\n"+
			                "{"                                                                    +"\n"+
			                "struct group *data;"                                                  +"\n"+
			                "int i;"                                                               +"\n"+
			                "while((data= getgrent())!=0){"                                        +"\n"+
			                "i=0;"                                                                 +"\n"+
			                "printf(\"%s:%s:%d:\",data->gr_name,data->gr_passwd,data->gr_gid);"      +"\n"+
			                "while(data->gr_mem[i])printf(\"%s,\",data->gr_mem[i++]);"               +"\n"+
			                "printf(\"\\n\");"                                                        +"\n"+
			                "}"                                                                    +"\n"+
			                "}"                                                                    
			                ,
				            "gcc"
				            ,
				            "PWD"
				            ,
			                },
				 });
	 }

}
