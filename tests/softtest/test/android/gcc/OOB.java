package softtest.test.android.gcc;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

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

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

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
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;

@RunWith(Parameterized.class)
public class OOB {
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/gcc/fault/OOB-0.1.xml";
	FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	
	static Pretreatment pre=new Pretreatment();
	static InterContext interContext = InterContext.getInstance();
	static int testcaseNum=0;
	String temp;//预处理后的中间文件
	
	public OOB(String source,String compiletype, String result)
	{
		this.source=source;	
		this.compiletype=compiletype;
		this.result = result;
	}

	@BeforeClass
	public static void setUpBase()
	{
		//根据待测试模式XML文件路径初始化自动机列表
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		CAnalysis.deleteAndCreateTemp(Config.PRETREAT_DIR);
		pre.setPlatform(PlatformType.GCC);
		String INCLUDE = System.getenv("GCCINC");
		if(INCLUDE==null){
			throw new RuntimeException("System environment variable \"GCCINC\" error!");
		}
		String[] Inctemp = INCLUDE.split(";");
		//将GCCINC中的头文件目录，自动识别为头文件目录
		List<String> include = new ArrayList<String>();
		for(int i = 0;i<Inctemp.length;i++){
			Pretreatment.systemInc.add(Inctemp[i]);
			include.add(Inctemp[i]);
		}
		pre.setInclude(include);
		//ZYS:最好根据状态机描述文件XML中的相关字段读取出该模式所属于的故障类别
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);

		Config.REGRESS_RULE_TEST=true;
	}
	
	//根据不同的模式需求，自行分配当前AST分析到的步骤
	private void analysis(ASTTranslationUnit astroot){
		astroot.jjtAccept(new ScopeAndDeclarationFinder(), null);
		astroot.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
		
		//清空原有全局分析中产生的函数摘要信息
		InterCallGraph.getInstance().clear();
		astroot.jjtAccept(new InterMethodVisitor(), null);
		
		CGraph g = new CGraph();
		((AbstractScope)(astroot.getScope())).resolveCallRelation(g);
		List<CVexNode> list = g.getTopologicalOrderList();
		Collections.reverse(list);
		
		ControlFlowData flow = new ControlFlowData();
		ControlFlowVisitor cfv = new ControlFlowVisitor();
		ControlFlowDomainVisitor cfd = new ControlFlowDomainVisitor();
		
		for (CVexNode cvnode : list) {
			SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
			if (node instanceof ASTFunctionDefinition) {
				cfv.visit((ASTFunctionDefinition)node, flow);
				cfd.visit((ASTFunctionDefinition)node, null);
			} 
		}
		
		astroot.jjtAccept(fsmAnalysis, cfData);
		
		assertEquals(result,getFSMAnalysisResult());
	}
	
	private String getFSMAnalysisResult()
	{
		List<Report> reports=cfData.getReports();
		String analysisResult=null;
		if(reports.size()==0)
		{
			analysisResult="OK";
			return analysisResult;
		}
		for(Report r:reports)
		{
			analysisResult=r.getFsmName();
			System.out.println(r.getFsmName()+" : "+r.getDesp());
		}
		return analysisResult;
	}

	@Before
	public void init() {
		cfData = new FSMControlFlowData();
		List<Report> reports = new ArrayList<Report>();
		cfData.setReports(reports);
		fsmAnalysis=new FSMAnalysisVisitor(cfData); 
		
		//将测试用例中的代码行，写到temp中形成.c源文件；
		String tempName="testcase_"+ (testcaseNum++) +".c";
		File tempFile=new File(Config.PRETREAT_DIR +"\\"+ tempName);
		if (Config.DELETE_PRETREAT_FILES) {
			tempFile.deleteOnExit();
		}
		FileWriter fw;
		try {
			fw = new FileWriter(tempFile);
			fw.write(source);
			fw.flush();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		temp=pre.pretreat(tempFile.getAbsolutePath(),  pre.getInclude(), new ArrayList<String>());
		
		//根据当前检测的测试用例，载入相关的库函数摘要
		
	}

	@After
	public void shutdown() {
	
	}

	@Test
	public void test() {
		try {
			CParser.setType("gcc");
			CParser parser_gcc;
			parser_gcc = CParser.getParser(new CCharStream(new FileInputStream(temp)));
			CParser.setType("keil");
			CParser parser_keil = CParser.getParser(new CCharStream(new FileInputStream(temp)));
			ASTTranslationUnit gcc_astroot=null,keil_astroot=null;
			if(compiletype.equals("gcc")){
				CParser.setType("gcc");
				try {
					gcc_astroot = parser_gcc.TranslationUnit();
				} catch (ParseException e) {
					e.printStackTrace();
					fail("parse error");
				}
				analysis(gcc_astroot); 
			}else if(compiletype.equals("keil")){
				CParser.setType("keil");
				try {
					keil_astroot= parser_keil.TranslationUnit();
				} catch (ParseException e) {
					e.printStackTrace();
					fail("parse error");
				}
				analysis(keil_astroot);
			}else{
				CParser.setType("gcc");
				try {
					gcc_astroot = parser_gcc.TranslationUnit();
				} catch (ParseException e) {
					e.printStackTrace();
					fail("parse error");
				}
				pre.setPlatform(PlatformType.GCC);
				analysis(gcc_astroot);
				
				CParser.setType("keil");
				try {
					keil_astroot= parser_keil.TranslationUnit();
				} catch (ParseException e) {
					e.printStackTrace();
					fail("parse error");
				}
				pre.setPlatform(PlatformType.KEIL);
				analysis(keil_astroot);
			}
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
		}
	}
	
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
	/////////////////  0   ///////////////////	
				 //循环区间，需要修改
		            {
		            "void f(int use_order)"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	    int array[2];"                                                   +"\n"+
		            "		int m;"                                                             +"\n"+
		            "		for (m = use_order - 1; m > 0; m--)"                                +"\n"+
		            "		        array[m]= 1;"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  1  ///////////////////	
		          //这个在跑android工程的时候报出了OOB，但在测试用例中是正常的  -- nmh
		            {
		             "static const int init_jk[] = {2,3,4,6}; /* initial value for jk */"   +"\n"+
		             "int __kernel_rem_pio2(int prec)"                                      +"\n"+
		             "{"                                                                    +"\n"+
		             "	int jk;"                                                             +"\n"+
		             ""                                                                     +"\n"+
		             "    /* initialize jk*/"                                               +"\n"+
		             "	jk = init_jk[prec];"                                                 +"\n"+
		             "}"                                                                    
		             ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		   /////////////////  2  ///////////////////
		            //这个在跑android工程和DTS配置跑的时候报出了OOB  -- nmh
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
	/////////////////  3   ///////////////////	
		  //这个在跑android工程报出35处IP，DTS配置跑的时候报出24处IP  -- nmh
		            //E:\android\bionic\libm\src\k_rem_pio2.c
		            {
		            "typedef int int32_t;"                                                 +"\n"+
		            ""                                                                     +"\n"+
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
		            "	int __kernel_rem_pio2(double *x, double *y, int e0, int nx, int prec, const int32_t *ipio2)"+"\n"+
		            "{"                                                                    +"\n"+
		            "	int32_t jz,jx,jv,jp,jk,carry,n,iq[20],i,j,k,m,q0,ih;"                +"\n"+
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
		            "	jz = jk;"                                                            +"\n"+
		            "recompute:"                                                           +"\n"+
		            "    /* distill q[] into iq[] reversingly */"                          +"\n"+
		            "	for(i=0,j=jz,z=q[jz];j>0;i++,j--) {"                                 +"\n"+
		            "	    fw    =  (double)((int32_t)(twon24* z));"                        +"\n"+
		            "	    iq[i] =  (int32_t)(z-two24*fw);"                                 +"\n"+
		            "	    z     =  q[j-1]+fw;"                                             +"\n"+
		            "	}"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "    /* compute n */"                                                  +"\n"+
		            "	z  = scalbn(z,q0);		/* actual value of z */"                         +"\n"+
		            "	z -= 8.0*floor(z*0.125);		/* trim off integer >= 8 */"               +"\n"+
		            "	n  = (int32_t) z;"                                                   +"\n"+
		            "	z -= (double)n;"                                                     +"\n"+
		            "	ih = 0;"                                                             +"\n"+
		            "	if(q0>0) {	/* need iq[jz-1] to determine n */"                       +"\n"+
		            "	    i  = (iq[jz-1]>>(24-q0)); n += i;"                               +"\n"+
		            "	    iq[jz-1] -= i<<(24-q0);"                                         +"\n"+
		            "	    ih = iq[jz-1]>>(23-q0);"                                         +"\n"+
		            "	}"                                                                   +"\n"+
		            "	else if(q0==0) ih = iq[jz-1]>>23;"                                   +"\n"+
		            "	else if(z>=0.5) ih=2;"                                               +"\n"+
		            ""                                                                     +"\n"+
		            "	if(ih>0) {	/* q > 0.5 */"                                            +"\n"+
		            "	    n += 1; carry = 0;"                                              +"\n"+
		            "	    for(i=0;i<jz ;i++) {	/* compute 1-q */"                          +"\n"+
		            "		j = iq[i];"                                                         +"\n"+
		            "		if(carry==0) {"                                                     +"\n"+
		            "		    if(j!=0) {"                                                     +"\n"+
		            "			carry = 1; iq[i] = 0x1000000- j;"                                  +"\n"+
		            "		    }"                                                              +"\n"+
		            "		} else  iq[i] = 0xffffff - j;"                                      +"\n"+
		            "	    }"                                                               +"\n"+
		            "	    if(q0>0) {		/* rare case: chance is 1 in 12 */"                  +"\n"+
		            "	        switch(q0) {"                                                +"\n"+
		            "	        case 1:"                                                     +"\n"+
		            "	    	   iq[jz-1] &= 0x7fffff; break;"                                +"\n"+
		            "	    	case 2:"                                                        +"\n"+
		            "	    	   iq[jz-1] &= 0x3fffff; break;"                                +"\n"+
		            "	        }"                                                           +"\n"+
		            "	    }"                                                               +"\n"+
		            "	    if(ih==2) {"                                                     +"\n"+
		            "		z = one - z;"                                                       +"\n"+
		            "		if(carry!=0) z -= scalbn(one,q0);"                                  +"\n"+
		            "	    }"                                                               +"\n"+
		            "	}"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "    /* check if recomputation is needed */"                           +"\n"+
		            "	if(z==zero) {"                                                       +"\n"+
		            "	    j = 0;"                                                          +"\n"+
		            "	    for (i=jz-1;i>=jk;i--) j |= iq[i];"                              +"\n"+
		            "	    if(j==0) { /* need recomputation */"                             +"\n"+
		            "		for(k=1;iq[jk-k]==0;k++);   /* k = no. of terms needed */"          +"\n"+
		            ""                                                                     +"\n"+
		            "		for(i=jz+1;i<=jz+k;i++) {   /* add q[jz+1] to q[jz+k] */"           +"\n"+
		            "		    f[jx+i] = (double) ipio2[jv+i];"                                +"\n"+
		            "		    for(j=0,fw=0.0;j<=jx;j++) fw += x[j]*f[jx+i-j];"                +"\n"+
		            "		    q[i] = fw;"                                                     +"\n"+
		            "		}"                                                                  +"\n"+
		            "		jz += k;"                                                           +"\n"+
		            "		goto recompute;"                                                    +"\n"+
		            "	    }"                                                               +"\n"+
		            "	}"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "    /* chop off zero terms */"                                        +"\n"+
		            "	if(z==0.0) {"                                                        +"\n"+
		            "	    jz -= 1; q0 -= 24;"                                              +"\n"+
		            "	    while(iq[jz]==0) { jz--; q0-=24;}"                               +"\n"+
		            "	} else { /* break z into 24-bit if necessary */"                     +"\n"+
		            "	    z = scalbn(z,-q0);"                                              +"\n"+
		            "	    if(z>=two24) {"                                                  +"\n"+
		            "		fw = (double)((int32_t)(twon24*z));"                                +"\n"+
		            "		iq[jz] = (int32_t)(z-two24*fw);"                                    +"\n"+
		            "		jz += 1; q0 += 24;"                                                 +"\n"+
		            "		iq[jz] = (int32_t) fw;"                                             +"\n"+
		            "	    } else iq[jz] = (int32_t) z ;"                                   +"\n"+
		            "	}"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "    /* convert integer \"bit\" chunk to floating-point value */"        +"\n"+
		            "	fw = scalbn(one,q0);"                                                +"\n"+
		            "	for(i=jz;i>=0;i--) {"                                                +"\n"+
		            "	    q[i] = fw*(double)iq[i]; fw*=twon24;"                            +"\n"+
		            "	}"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "    /* compute PIo2[0,...,jp]*q[jz,...,0] */"                         +"\n"+
		            "	for(i=jz;i>=0;i--) {"                                                +"\n"+
		            "	    for(fw=0.0,k=0;k<=jp&&k<=jz-i;k++) fw += PIo2[k]*q[i+k];"        +"\n"+
		            "	    fq[jz-i] = fw;"                                                  +"\n"+
		            "	}"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "    /* compress fq[] into y[] */"                                     +"\n"+
		            "	switch(prec) {"                                                      +"\n"+
		            "	    case 0:"                                                         +"\n"+
		            "		fw = 0.0;"                                                          +"\n"+
		            "		for (i=jz;i>=0;i--) fw += fq[i];"                                   +"\n"+
		            "		y[0] = (ih==0)? fw: -fw;"                                           +"\n"+
		            "		break;"                                                             +"\n"+
		            "	    case 1:"                                                         +"\n"+
		            "	    case 2:"                                                         +"\n"+
		            "		fw = 0.0;"                                                          +"\n"+
		            "		for (i=jz;i>=0;i--) fw += fq[i];"                                   +"\n"+
		            "		y[0] = (ih==0)? fw: -fw;"                                           +"\n"+
		            "		fw = fq[0]-fw;"                                                     +"\n"+
		            "		for (i=1;i<=jz;i++) fw += fq[i];"                                   +"\n"+
		            "		y[1] = (ih==0)? fw: -fw;"                                           +"\n"+
		            "		break;"                                                             +"\n"+
		            "	    case 3:	/* painful */"                                           +"\n"+
		            "		for (i=jz;i>0;i--) {"                                               +"\n"+
		            "		    fw      = fq[i-1]+fq[i];"                                       +"\n"+
		            "		    fq[i]  += fq[i-1]-fw;"                                          +"\n"+
		            "		    fq[i-1] = fw;"                                                  +"\n"+
		            "		}"                                                                  +"\n"+
		            "		for (i=jz;i>1;i--) {"                                               +"\n"+
		            "		    fw      = fq[i-1]+fq[i];"                                       +"\n"+
		            "		    fq[i]  += fq[i-1]-fw;"                                          +"\n"+
		            "		    fq[i-1] = fw;"                                                  +"\n"+
		            "		}"                                                                  +"\n"+
		            "		for (fw=0.0,i=jz;i>=2;i--) fw += fq[i];"                            +"\n"+
		            "		if(ih==0) {"                                                        +"\n"+
		            "		    y[0] =  fq[0]; y[1] =  fq[1]; y[2] =  fw;"                      +"\n"+
		            "		} else {"                                                           +"\n"+
		            "		    y[0] = -fq[0]; y[1] = -fq[1]; y[2] = -fw;"                      +"\n"+
		            "		}"                                                                  +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return n&7;"                                                         +"\n"+
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
