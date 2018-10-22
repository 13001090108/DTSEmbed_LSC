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
public class NPD extends ModelTestBase {
	public NPD(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);

		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/npd_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		libManager.loadSingleLibFile("gcc_lib/lib_summary.xml");
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	@Parameters
	public static Collection<Object[]> testcaseAndResults()
	{
		return Arrays.asList(new Object[][] {
				/////////////////  0 /////////////////////////	
				//这个在跑android工程的时候报出了NPD，但在测试用例中是正常的  -- nmh
	            {
	                "#define M   16"                                                       +"\n"+
	                "void Levinson()"                                                      +"\n"+
	                "{"                                                                    +"\n"+
	                "	int i, j;"                                                           +"\n"+
	                "	int Anh[M + 1], Anl[M + 1];"                                         +"\n"+
	                ""                                                                     +"\n"+
	                "	for (i = 2; i <= M; i++)"                                            +"\n"+
	                "	{"                                                                   +"\n"+
	                "		for (j = 1; j < i; j++)"                                            +"\n"+
	                "		{"                                                                  +"\n"+
	                "			Anh[j] = 1;"                                                       +"\n"+
	                "			Anl[j] = 2;"                                                       +"\n"+
	                "		}"                                                                  +"\n"+
	                ""                                                                     +"\n"+
	                "	}"                                                                   +"\n"+
	                "	return;"                                                             +"\n"+
	                "}"                                                                    
	                ,
					"gcc"
					,
					"OK"
					,
				},			
				/////////////////  1 /////////////////////////	
				//跑整个android工程时出现问题，但是但跑一个.i文件没有问题，测试用例中也没有问题  -- nmh
	            {
		            "#define MAX_MB_SEGMENTS 10"                                           +"\n"+
		            "void vp8_loop_filter_frame(int default_filt_lvl)"                     +"\n"+
		            "{"                                                                    +"\n"+
		            "    int baseline_filter_level[MAX_MB_SEGMENTS];"                      +"\n"+
		            ""                                                                     +"\n"+
		            "    for (i = 0; i < MAX_MB_SEGMENTS; i++)"                        +"\n"+
		            "            baseline_filter_level[i] = default_filt_lvl;"             +"\n"+
		            "}"                                                                    
		            ,
					"gcc"
					,
					"OK"
					,
				},
				   /////////////////  2  ///////////////////
	            ////这个在跑android工程的时候报出了NPD，但在测试用例中是正常的  -- nmh
	            {
	            "static const int init_jk[] = {2,3,4,6}; /* initial value for jk */"   +"\n"+
	            ""                                                                     +"\n"+
	            "static const double PIo2[] = {"                                       +"\n"+
	            "  1.57079625129699707031e+00, /* 0x3FF921FB, 0x40000000 */"           +"\n"+
	            "  7.54978941586159635335e-08, /* 0x3E74442D, 0x00000000 */"           +"\n"+
	            "  5.39030252995776476554e-15, /* 0x3CF84698, 0x80000000 */"           +"\n"+
	            "  3.28200341580791294123e-22, /* 0x3B78CC51, 0x60000000 */"           +"\n"+
	            "  1.27065575308067607349e-29, /* 0x39F01B83, 0x80000000 */"           +"\n"+
	            "  1.22933308981111328932e-36, /* 0x387A2520, 0x40000000 */"           +"\n"+
	            "  2.73370053816464559624e-44, /* 0x36E38222, 0x80000000 */"           +"\n"+
	            "  2.16741683877804819444e-51, /* 0x3569F31D, 0x00000000 */"           +"\n"+
	            "};"                                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "static const double"                                                  +"\n"+
	            "zero   = 0.0,"                                                        +"\n"+
	            "one    = 1.0,"                                                        +"\n"+
	            "two24   =  1.67772160000000000000e+07, /* 0x41700000, 0x00000000 */"  +"\n"+
	            "twon24  =  5.96046447753906250000e-08; /* 0x3E700000, 0x00000000 */"  +"\n"+
	            ""                                                                     +"\n"+
	            "	int __kernel_rem_pio2(double *x, double *y, int e0, int nx, int prec, const int *ipio2)"+"\n"+
	            "{"                                                                    +"\n"+
	            "	int jz,jx,jv,jp,jk,carry,n,iq[20],i,j,k,m,q0,ih;"                    +"\n"+
	            "	double z,fw,f[20],fq[20],q[20];"                                     +"\n"+
	            ""                                                                     +"\n"+
	            "    /* initialize jk*/"                                               +"\n"+
	            "	jk = init_jk[prec];"                                                 +"\n"+
	            "	jp = jk;"                                                            +"\n"+
	            ""                                                                     +"\n"+
	            "    /* determine jx,jv,q0, note that 3>q0 */"                         +"\n"+
	            "	jx =  nx-1;"                                                         +"\n"+
	            "	jv = (e0-3)/24; if(jv<0) jv=0;"                                      +"\n"+
	            "	q0 =  e0-24*(jv+1);"                                                 +"\n"+
	            ""                                                                     +"\n"+
	            "    /* set up f[0] to f[jx+jk] where f[jx+jk] = ipio2[jv+jk] */"      +"\n"+
	            "	j = jv-jx; m = jx+jk;"                                               +"\n"+
	            "	for(i=0;i<=m;i++,j++) f[i] = (j<0)? zero : (double) ipio2[j];"       +"\n"+
	            ""                                                                     +"\n"+
	            "    /* compute q[0],q[1],...q[jk] */"                                 +"\n"+
	            "	for (i=0;i<=jk;i++) {"                                               +"\n"+
	            "	    for(j=0,fw=0.0;j<=jx;j++) fw += x[j]*f[jx+i-j]; q[i] = fw;"      +"\n"+
	            "	}"                                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },	
				/////////////////  3 /////////////////////////	
				//  -- nmh
	            {
	                "static inline char * strip_end(char *str)"                            +"\n"+
	                "{"                                                                    +"\n"+
	                "    char *end = str + strlen(str) - 1;"                               +"\n"+
	                ""                                                                     +"\n"+
	                "    while (end >= str && isspace(*end))"                              +"\n"+
	                "        *end-- = '\\0';"                                               +"\n"+
	                "    return str;"                                                      +"\n"+
	                "}"                                                                    
	                ,
					"gcc"
					,
					"OK"
					,
				},	   
				/////////////////  4 /////////////////////////	
				//这个在跑android工程的时候报出了NPD，但在dts配置和回归用例中是正常的   -- nmh
	            {
		            "void xmlParseCharEncoding(const char* name)"                          +"\n"+
		            "{"                                                                    +"\n"+
		            "    char upper[500];"                                                 +"\n"+
		            "    int i;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "    for (i = 0;i < 499;i++) {"                                        +"\n"+
		            "        upper[i] = toupper(name[i]);"                                 +"\n"+
		            "	     if (upper[i] == 0) break;"                                           +"\n"+
		            "    }"                                                                +"\n"+
		            "    upper[i] = 0;"                                                    +"\n"+
		            "}"                                                                    
		            ,
					"gcc"
					,
					"OK"
					,
				},	
				/////////////////  5 /////////////////////////	
				//这个在跑android工程的时候报出了NPD，但在dts配置和回归用例中是正常的   -- nmh
	            {
		            "void CLG( int size, char* cost)"                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "    int i;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "    if (!cost) return;"                                               +"\n"+
		            ""                                                                     +"\n"+
		            "    for(i=0; i<size; i++)"                                            +"\n"+
		            "	   cost[i] = 0;"                                                     +"\n"+
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
