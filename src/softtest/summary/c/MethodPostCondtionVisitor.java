package softtest.summary.c;

import java.util.Hashtable;

import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.interval.Domain;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;

/**
 * 
 * @author 祁鹏
 */
public class MethodPostCondtionVisitor implements MethodFeatureVisitor {

	private static MethodPostCondtionVisitor instance;
	
	private MethodPostCondtionVisitor() {	
	}
	
	public static MethodPostCondtionVisitor getInstance() {
		if (instance == null) {
			instance = new MethodPostCondtionVisitor(); 
		}
		return instance;
	}
	
	/**
	 * zys:在函数出口处，记录所有该函数对外部变量的修改:
	 * 		目前仅考虑全局变量，对指针、引用形式的参数暂时不处理
	 */
	public void visit(VexNode vexNode) {
		MethodPostCondition feature = new MethodPostCondition();
		Hashtable<VariableNameDeclaration, Domain> table=vexNode.getVarDomainSet().getTable();
		for(VariableNameDeclaration var:table.keySet())
		{
			if(var.getScope() instanceof SourceFileScope)
			{
				Variable variable = Variable.getVariable(var);
				if (variable != null) {
					Domain d=table.get(var);
					//zys 2011.6.24	只对发生确定性改变的全局变量生成后置摘要
					if(d!=null && !d.isUnknown() && !Domain.isEmpty(d))
						feature.addDomain(variable, table.get(var));
				}
			}
		}
		
		// 将计算出的函数特性添加到函数摘要中
		MethodSummary summary = InterContext.getMethodSummary(vexNode);
		if (summary != null && !feature.isEmpty()) {
			summary.addPostCondition(feature);
			if (Config.INTER_METHOD_TRACE) {
				MethodNameDeclaration methodDecl = InterContext.getMethodDecl(vexNode);
				if (methodDecl != null) {
					System.err.println(methodDecl.getFullName() + " " + feature);
				}
			}
		}
	}
}
