package softtest.test.c.hwchecklist;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.ByteArrayInputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

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
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.fsmanalysis.c.FSMControlFlowData;
import softtest.fsmanalysis.c.Report;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterMethodVisitor;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
/**
 * 
 * @author Pzq
 *
 */
@RunWith(Parameterized.class)
public class Test_MLV {
    private String source = null;

    private String compiletype = null;

    private String result = null;

    private static final String fsmPath = "softtest/rules/gcc/rule/HW_6_1_MLV-0.1.xml";

    FSMAnalysisVisitor fsmAnalysis;

    private FSMControlFlowData cfData;

    public Test_MLV(String source, String compiletype, String result) {
        this.source = source;
        this.compiletype = compiletype;
        this.result = result;
    }

    @BeforeClass
    public static void setUpBase() {
        BasicConfigurator.configure();
        PropertyConfigurator.configure("log4j.properties");
        // 根据待测试模式XML文件路径初始化自动机列表
        FSMMachine fsm = FSMLoader.loadXML(fsmPath);

        // ZYS:最好根据状态机描述文件XML中的相关字段读取出该模式所属于的故障类别
        fsm.setType("fault");
        // 每次加入自动机前都清空一下原来的fsms
        FSMAnalysisVisitor.clearFSMS();
        FSMAnalysisVisitor.addFSMS(fsm);

        Config.REGRESS_RULE_TEST = true;
    }

    // 根据不同的模式需求，自行分配当前AST分析到的步骤
    private void analysis(ASTTranslationUnit astroot) {
        astroot.jjtAccept(new ScopeAndDeclarationFinder(), null);
        astroot.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
        // 清空原有全局分析中产生的函数摘要信息
        InterCallGraph.getInstance().clear();
        astroot.jjtAccept(new InterMethodVisitor(), null);

        CGraph g = new CGraph();
        ((AbstractScope) (astroot.getScope())).resolveCallRelation(g);
        List<CVexNode> list = g.getTopologicalOrderList();
        Collections.reverse(list);

        ControlFlowData flow = new ControlFlowData();
        ControlFlowVisitor cfv = new ControlFlowVisitor();
        ControlFlowDomainVisitor cfd = new ControlFlowDomainVisitor();

        for (CVexNode cvnode : list) {
            SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
            if (node instanceof ASTFunctionDefinition) {
                cfv.visit((ASTFunctionDefinition) node, flow);
                cfd.visit((ASTFunctionDefinition) node, null);
            }
        }
        astroot.jjtAccept(new DUAnalysisVisitor(), null);
        astroot.jjtAccept(fsmAnalysis, cfData);
        assertEquals(result, getFSMAnalysisResult());
    }

    private String getFSMAnalysisResult() {
        List<Report> reports = cfData.getReports();
        String analysisResult = null;
        if (reports.size() == 0) {
            analysisResult = "OK";
            return analysisResult;
        }
        System.out.println("本次检测共报告了" + reports.size() + "个故障点");
        for (Report r : reports) {
            analysisResult = r.getFsmName();
            System.out.println("\t" + r.getFsmName() + " : " + r.getDesp());
        }
        return analysisResult;
    }

    @Before
    public void init() {
        cfData = new FSMControlFlowData();
        List<Report> reports = new ArrayList<Report>();
        cfData.setReports(reports);
        fsmAnalysis = new FSMAnalysisVisitor(cfData);
    }

    @After
    public void shutdown() {
        // 清除临时文件夹
    }

    @Test
    public void test() {
        CParser.setType("gcc");
        CParser parser_gcc = CParser.getParser(new CCharStream(
                new ByteArrayInputStream(source.getBytes())));
        CParser.setType("keil");
        CParser parser_keil = CParser.getParser(new CCharStream(
                new ByteArrayInputStream(source.getBytes())));
        ASTTranslationUnit gcc_astroot = null, keil_astroot = null;
        if (compiletype.equals("gcc")) {
            CParser.setType("gcc");
            try {
                gcc_astroot = parser_gcc.TranslationUnit();
            } catch (ParseException e) {
                e.printStackTrace();
                fail("parse error");
            }
            analysis(gcc_astroot);
        } else if (compiletype.equals("keil")) {
            CParser.setType("keil");
            try {
                keil_astroot = parser_keil.TranslationUnit();
            } catch (ParseException e) {
                e.printStackTrace();
                fail("parse error");
            }
            analysis(keil_astroot);
        } else {
            CParser.setType("gcc");
            try {
                gcc_astroot = parser_gcc.TranslationUnit();
            } catch (ParseException e) {
                e.printStackTrace();
                fail("parse error");
            }
            analysis(gcc_astroot);

            CParser.setType("keil");
            try {
                keil_astroot = parser_keil.TranslationUnit();
            } catch (ParseException e) {
                e.printStackTrace();
                fail("parse error");
            }
            analysis(keil_astroot);
        }
    }

    @Parameters
    public static Collection<Object[]> testcaseAndResults() {
        return Arrays.asList(new Object[][] {
        		
/////////////////  0   ///////////////////	
                {
                "void f()"                                                             +"\n"+
                "{"                                                                    +"\n"+
                "int i;"                                                               +"\n"+
                " 	for(i=10; i>0;){"                                                   +"\n"+
                "     int flag=getflag();"                                             +"\n"+
                "     if(flag)"                                                        +"\n"+
                "        i++;"                                                         +"\n"+
                "     else"                                                            +"\n"+
                "        i--;"                                                         +"\n"+
                " 	}"                                                                  +"\n"+
                "}"                                                                    
                ,
                "gcc"
                ,
                "HW_6_1_MLV"
                ,
                },
                
/////////////////  1   ///////////////////	
                {
                "void f(int i)"                                                        +"\n"+
                "{"                                                                    +"\n"+
                " 	while(i>0){"                                                        +"\n"+
                "     int flag=getflag();"                                             +"\n"+
                "     if(flag)"                                                        +"\n"+
                "        i--;"                                                         +"\n"+
                "     else"                                                            +"\n"+
                "        i--;"                                                         +"\n"+
                " 	}"                                                                  +"\n"+
                "}"                                                                    
                ,
                "gcc"
                ,
                "OK"
                ,
                },
                
/////////////////  2   ///////////////////	
                {
                "void f(int i)"                                                        +"\n"+
                "{"                                                                    +"\n"+
                " 	while(i>0){"                                                        +"\n"+
                "     int flag=getflag();"                                             +"\n"+
                "     if(flag)"                                                        +"\n"+
                "        i++;"                                                         +"\n"+
                "     else"                                                            +"\n"+
                "        i--;"                                                         +"\n"+
                " 	}"                                                                  +"\n"+
                "}"                                                                    
                ,
                "gcc"
                ,
                "HW_6_1_MLV"
                ,
                },
                
/////////////////  3   ///////////////////	
                {
                "int i;"                                                               +"\n"+
                "void f()"                                                             +"\n"+
                "{"                                                                    +"\n"+
                " 	do{"                                                                +"\n"+
                "     int flag=getflag();"                                             +"\n"+
                "     if(flag)"                                                        +"\n"+
                "        i++;"                                                         +"\n"+
                "     else"                                                            +"\n"+
                "        i--;"                                                         +"\n"+
                " 	}while(i>0);"                                                       +"\n"+
                "}"                                                                    
                ,
                "gcc"
                ,
                "HW_6_1_MLV"
                ,
                },

/////////////////  4   ///////////////////	
                {
                "int i;"                                                               +"\n"+
                "void f()"                                                             +"\n"+
                "{"                                                                    +"\n"+
                " 	do{"                                                                +"\n"+
                "     int flag=getflag();"                                             +"\n"+
                "     if(flag)"                                                        +"\n"+
                "        i++;"                                                         +"\n"+
                "     else"                                                            +"\n"+
                "        i++;"                                                         +"\n"+
                " 	}while(i>0);"                                                       +"\n"+
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
