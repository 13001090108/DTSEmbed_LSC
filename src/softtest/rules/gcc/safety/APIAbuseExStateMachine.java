package softtest.rules.gcc.safety;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.SimpleNode;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.Method;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MethodAPIAbuseFeature;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.Type.CType;

/**
 * <p>
 * Create the state machines to check API abuse. 
 * </p>
 * @author liuyan
 *
 */
public class APIAbuseExStateMachine {

	public static List<FSMMachineInstance> createAPIAbuseStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		
		String xPath=".//UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true'] " +
			"|.//Expression/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);

		for (SimpleNode funcNode : evaluationResults) {
			
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(funcNode);
			if (methodDecl == null)
				continue;
			
			if(methodDecl.getImage().equals("GetTempFileNameA")){
				String desp = "安全的创建临时文件：有些临时文件名是很危险的，因为这样可能会让黑客提前猜到它们的名字，从而导致黑客可以访问专用数据";
				FSMMachineInstance fsmInstance = fsm.creatInstance();
				fsmInstance.setRelatedASTNode(funcNode);
				fsmInstance.setResultString(funcNode.getImage());
				fsmInstance.setDesp(desp);
				list.add(fsmInstance);
			}
			
			if (methodDecl.getMethodSummary() == null)
				continue;
			int a=1;
			int b=2;
			
			
			
			MethodAPIAbuseFeature apiAbuseFeature = (MethodAPIAbuseFeature)methodDecl.getMethodSummary().findMethodFeature(MethodAPIAbuseFeature.class);
			if (apiAbuseFeature == null)
				continue;
			
			FSMMachineInstance fsmInstance = fsm.creatInstance();
			fsmInstance.setRelatedASTNode(funcNode);
			fsmInstance.setResultString(funcNode.getImage());
			fsmInstance.setDesp(apiAbuseFeature.getDescription());
			
			list.add(fsmInstance);
		}

		return list;
	}

}


