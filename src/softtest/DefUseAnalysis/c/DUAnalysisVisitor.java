package softtest.DefUseAnalysis.c;

import java.io.IOException;
import org.apache.log4j.Logger;
import softtest.DefUseAnalysis.c.DumpUseDefRelation;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTNestedFunctionDefinition;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CParserVisitorAdapter;
import softtest.cfg.c.Graph;
import softtest.config.c.Config;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.MethodNameDeclaration;

public class DUAnalysisVisitor extends CParserVisitorAdapter
{
	static Logger logger = Logger.getLogger(DUAnalysisVisitor.class);
	
	@Override
	public Object visit(ASTTranslationUnit node, Object data)
	{
		//初始化变量出现的定义使用类型
		((AbstractScope)(node.getScope())).initDefUse();
		return super.visit(node, data);
	}
	
	@Override
	public Object visit(ASTFunctionDefinition node, Object data)
	{
		Graph g = node.getGraph();
		if (g == null) {
			return null;
		}
		g.numberOrderVisit(new DUControlFlowVisitor(), data);
		
		dump(g, node.getDecl());
		
		return null;
	}

	private void dump(Graph g, MethodNameDeclaration methodDecl) {
		// 输出到文件，测试用
		if(!Config.SKIP_METHODANALYSIS || Config.TRACE ){
			if(Config.MethodAnalysisDUAnalysisVisitor || Config.TRACE ){
				if (Config.DU || Config.TRACE) 
				{		
					String name = "temp/" + methodDecl.getImage();
					g.accept(new DumpUseDefRelation(), name + "_DU.dot");
					
					if(!Config.SKIP_METHODANALYSIS){
						if(Config.MethodAnalysisDUAnalysisVisitor){
							if(Config.DU){
								logger.info("【6 DU定义使用链】输出到了文件" + name + "_DU.dot");
							}
						}
					}

					System.out.println("控制流图(DU定义使用链）输出到了文件" + name + "_DU.dot");
					try {
						java.lang.Runtime.getRuntime().exec(
								"dot -Tjpg -o " + name + "_DU.jpg " + name + "_DU.dot")
								.waitFor();
					} catch (IOException e1) {
						System.out.println(e1);
						logger.error("请安装程序Graphvix后再运行程序");
						logger.error(e1);
					} catch (InterruptedException e2) {
						System.out.println(e2);
						logger.error("请安装程序Graphvix后再运行程序");
						logger.error(e2);
					}
					if(!Config.SKIP_METHODANALYSIS){
						if(Config.MethodAnalysisDUAnalysisVisitor){
							if(Config.DU){
								logger.info("【6 DU定义使用链】打印到了文件" + name + "_DU.jpg");
							}
						}
					}
					
					System.out.println("控制流图(DU定义使用链）打印到了文件" + name + "_DU.jpg");
				}
			}
		}
	}
	
	@Override
	public Object visit(ASTNestedFunctionDefinition node, Object data)
	{
		return null;
	}
}
