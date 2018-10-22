package softtest.test.c.hangtiancheng;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.ByteArrayInputStream;
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
import softtest.fsmanalysis.c.UnknownString;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.InterMethodVisitor;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.test.c.gcc.BaseTestCase;
import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class HW_6_1_DAB extends ModelTestBase{
    public HW_6_1_DAB(String source, String compiletype, String result) {
		super(source, compiletype, result);
	}

    @BeforeClass
    public static void setUpBase() {
    	fsmPath = "softtest/rules/gcc/rule/HW_6_1_DAB-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		pre.setPlatform(PlatformType.KEIL);
		
		List<String> include = new ArrayList<String>();
		
		String INCLUDE = System.getenv("C51INC");
		if(INCLUDE==null){
			throw new RuntimeException("System environment variable \"GCCINC\" error!");
		}
		String[] Inctemp = INCLUDE.split(";");
		include.add(Inctemp[0]);
		pre.setInclude(include);
		Config.REGRESS_RULE_TEST=true;
    }

    @Parameters
    public static Collection<Object[]> testcaseAndResults() {
        return Arrays.asList(new Object[][] {
/////////////////  0   ///////////////////	
                {
                "#define int16 int\nvoid f(int k)"                                                             +"\n"+
                "{"                                                                    +"\n"+
                "  data int16 i=0;"                                                    +"\n"+
                "  for(i=0;i<3000;i++){}"                                              +"\n"+
                "}"                                                                    
                ,
                "keil"
                ,
                "OK"
                ,
                },


        });
    }
}
