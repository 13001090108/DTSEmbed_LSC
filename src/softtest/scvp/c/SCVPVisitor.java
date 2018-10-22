package softtest.scvp.c;


import java.io.FileWriter;
import java.io.IOException;


import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.CParserVisitorAdapter;
import softtest.cfg.c.Graph;
import softtest.dscvp.c.NameOccurrenceHashtableVisitor;
import softtest.interpro.c.Method;

public class SCVPVisitor extends CParserVisitorAdapter {
	@Override
	public Object visit(ASTFunctionDefinition node, Object data)
	{
		Graph g = node.getGraph();
		if (g == null) {
			return null;
		}
		
		// added by cmershen,2016.5.3
		g.numberOrderVisit(new SCVPControlFlowVisitor(), data);
		// added by cmershen,2016.5.17
		NameOccurrenceHashtableVisitor nhvisitor = new NameOccurrenceHashtableVisitor();
		g.numberOrderVisit(nhvisitor, data);
		
		// 分析函数副作用
		SideEffectsVisitor visitor = new SideEffectsVisitor();	
		g.numberOrderVisit(visitor, data);
		//输出函数调试信息到文件
		//added by cmershen 2016.12.13
//		try {
//			Method m = node.getDecl().getMethod();
//			String filename="c:\\scvp\\"+m.toString()+"_scvp.txt";
//			FileWriter fw = new FileWriter(filename, true);
//			
//			g.numberOrderVisit(new SCVPDumpVisitor(), fw);
//			
//			fw.append("前置摘要：\n");
//			fw.append(m.getCallerInfo().toString()+"\n");
//			
//			fw.append("后置摘要：\n");
//			fw.append(m.getExternalEffects().toString()+"\n");
//			
//			fw.append("返回值：\n");
//			fw.append(m.getReturnList().toString()+"\n");
//			
//			fw.close();
//		} catch (Exception e) {
//			e.printStackTrace();
//		}

		return null;
	}
	
}
