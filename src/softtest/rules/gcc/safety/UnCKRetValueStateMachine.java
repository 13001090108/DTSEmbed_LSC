package softtest.rules.gcc.safety;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.PointerDomain;
//import softtest.domain.cpp.PointDomain;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.Method;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MethodSummary;
import softtest.summary.c.MethodUnCKRetValuePostCondition;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.VariableNameDeclaration;

/**
 * Check if it's necessary to create the state machines for un-check return value of some specific function according to some regulars.
 * @author liuyan
 *
 */
public class UnCKRetValueStateMachine {
	
	/**Indicate the checking type*/
	enum CheckType {
		FEATURE, //The method to be checked occur in the "unck-ret-value_summary.xml"
		RET_DOMAIN, //The method to be checked occur in the "npd_summary.xml" or "rm_summary.xml" and it returns a "PointDomain"
	}
	
	private static final String DESP_EX = "：忽视方法的返回值会导致程序忽略意料之外的状态和情况";
	/**
	 * Calculate all the variables in the "if" expressions in the local analyzing function.
	 * @param node
	 * @param conditionVars
	 */
	private static void calculateCondVars(SimpleNode node, Map<VariableNameDeclaration, Integer> conditionVars) {
		String xPath = ".//SelectionStatement/Expression//PrimaryExpression[1]";
		//有点问题，跟CPP不是很一致
		List<SimpleNode> ifVarsNodes = StateMachineUtils.getEvaluationResults(node, xPath);
		
		for (SimpleNode varNode : ifVarsNodes) {
			VariableNameDeclaration varDecl = varNode.getVariableNameDeclaration();
			if (varDecl == null)
				continue;
			conditionVars.put(varDecl, varNode.getBeginLine());
		}
	}
	
	/**
	 * Check that if a variable is necessary to verify. it may not assign by a method which holds the MethodUnCKRetValuePostCondition feature.
	 * @param varNode
	 * @param funcNode
	 * @return
	 */
	private static boolean isNeedVerify(SimpleNode varNode, SimpleNode funcNode) {
		/*ASTassignment_expression assignmentNode = (ASTassignment_expression)funcNode.getFirstParentsOfType(ASTassignment_expression.class);
		if (assignmentNode == null)
			return false;
	
		if (varNode instanceof ASTqualified_id) {
			if (((SimpleNode)varNode.getFirstParentsOfType(ASTinit_declarator.class)).getFirstChildOfType(ASTassignment_expression.class) == assignmentNode) {
				return true;
			}
		}
		
		if (varNode instanceof ASTid_expression) {
			if (((SimpleNode)varNode.getFirstParentsOfType(ASTassignment_expression.class)).getFirstChildOfType(ASTassignment_expression.class) == assignmentNode) {
				return true;
			}
		}
		*/
		SimpleNode varStatementNode = (SimpleNode) varNode.getFirstParentOfType(ASTStatement.class);
		SimpleNode funcStatementNode = (SimpleNode) funcNode.getFirstParentOfType(ASTStatement.class);
		
		if (varStatementNode == funcStatementNode) {
			return true;
		}
		
		return false;
	}
	
	/**
	 * Check if a variable is in the if expression, if exists, it means that the code has checked the return value for the method.
	 * So not need to create a state machine.
	 * @param varNode
	 * @param conditionVars
	 * @return
	 */
	private static boolean isInConditionVars(SimpleNode varNode, Map<VariableNameDeclaration, Integer> conditionVars) {
		VariableNameDeclaration varDecl = varNode.getVariableNameDeclaration();
		//添加函数getSimpleVariable()
		if (varDecl == null) //not a variable, not need to create a state machine, so return true;
			return true;
		
		if (conditionVars.containsKey(varDecl)) { 
			int ifLine = conditionVars.get(varDecl);
			
			if (ifLine >= varNode.getBeginLine()) { //the if expression must come after the variable. this is to impersonate the flow sensitive.
				return true;
			}
		}
		
		return false;
	}
	
	/**
	 * Create the state machines.
	 * @param node
	 * @param fsm
	 * @return
	 */
	public static List<FSMMachineInstance> createUnckRetValStateMachines(SimpleNode node, FSMMachine fsm) {
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		/**
		 * Record all the variables occur in "if" expressions for the current method.
		 */
	    Map<VariableNameDeclaration, Integer> conditionVars = new HashMap<VariableNameDeclaration, Integer>();
		/**
		 * Indicate it has calculated the "conditonVars" or not.
		 */
	    boolean hasCalculatedCondVars = false;
	    
	    /**
	     * Record all the variables exist in the assignment or initial statements.
	     */
	    List<SimpleNode> varsNodes = null;
	    /**
	     * Indicate whether it has calculated all the assignment and initial statements for the current method.
	     */
	    boolean hasCalculatedAssAndInit = false;
	    
	    /**
	     * Get all the method nodes.
	     */
	    String xPath=".//UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true'] " +
				"|.//Expression/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
//	    String xPath=".//postfix_expression/primary_expression/id_expression[@Method='true']" +
//			"|.//declaration/declaration_specifiers/qualified_type/qualified_id[@Method='true']"+
//			"| .//postfix_expression[@SecondImage='.']/id_expression[@Method='true'] ";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
 
	    for (SimpleNode funcNode : evaluationResults) {
	    	CheckType ckType = null;
	    	
	    	MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(funcNode);
	    	if (methodDecl == null)
	    		continue;
	    	
	    	Method method = methodDecl.getMethod();
	    	if (method != null) {
	    		Domain retDomain = method.getReturnDomain();
	    		if (retDomain != null && retDomain instanceof PointerDomain) {
	    			ckType = CheckType.RET_DOMAIN;
	    		}
	    	}

			if (methodDecl.getMethodSummary() == null)
				continue;
			
	    	MethodUnCKRetValuePostCondition unCkRetValuePostCondition = null;
	    	
	    	MethodSummary mtSummary = methodDecl.getMethodSummary();
	    	if (mtSummary != null) {
	    		unCkRetValuePostCondition = (MethodUnCKRetValuePostCondition)methodDecl.getMethodSummary().findMethodFeature(MethodUnCKRetValuePostCondition.class);
	    		if( unCkRetValuePostCondition == null )
	    			continue;
	    		else{
	    			ckType = CheckType.FEATURE;
	    		}
	    		if (unCkRetValuePostCondition != null) {
	    			ckType = CheckType.FEATURE;
	    		}
	    	}
	    	
	    	if (ckType == null) {
	    		continue;
	    	}
	    	
	    	/** Describe the IP */
	    	String desp = "";
	    	if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {		
	    		desp = "use of fuction "+methodDecl.getImage()+",";
				if (ckType == CheckType.FEATURE) {
					desp += unCkRetValuePostCondition.getDescription();
				} else if (ckType == CheckType.RET_DOMAIN) {
					desp += "which returns a pointer";
				}
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				desp = "使用函数"+methodDecl.getImage()+",";
				if (ckType == CheckType.FEATURE) {
					desp += unCkRetValuePostCondition.getDescription();
				} else if (ckType == CheckType.RET_DOMAIN) {
					desp += "该函数返回指针类型";
				}
			}
	    	//it's necessary to calculate the variables which in the "if" expression.
	    	if (!hasCalculatedCondVars) {
	    		calculateCondVars(node, conditionVars);
	    		hasCalculatedCondVars = true;
	    	}
	    	
	    	/**
	    	 * Get the p in such format: HANDLE p; p = CreateNamedPipe(...) or HANDLE p = CreateNamedPipe(...) through "funcNode".
	    	 */
	    	if (!hasCalculatedAssAndInit) {
		    	xPath = ".//AssignmentExpression[./AssignmentOperator]/UnaryExpression//PrimaryExpression[@Method='false']" +
		    			"| .//InitDeclarator[./Initializer]/Declarator//DirectDeclarator";
		    	varsNodes = StateMachineUtils.getEvaluationResults(node, xPath);
		    	
		    	hasCalculatedAssAndInit = true;
	    	}
	    	
	    	/**
	    	 * Verify if the variables mentioned above in the following "if" expressions. 
	    	 */
	    	boolean isInAssorInitStatement = false;
	    	
	    	for (SimpleNode varNode : varsNodes) {
	    		//expel the variable not necessary to verify. such as p in p = fun(), where fun() doesn't hold the MethodUnCKRetValuePostCondition feature.
	    		if (!isNeedVerify(varNode, funcNode)) 
	    			continue;
	    		
	    		isInAssorInitStatement = true;
	    		
	    		if (!isInConditionVars(varNode, conditionVars)) {
	    			FSMMachineInstance fsmInstance = fsm.creatInstance();
	    			fsmInstance.setRelatedASTNode(funcNode);
	    			fsmInstance.setResultString(funcNode.getImage());
	    			if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
	    				fsmInstance.setDesp(desp + DESP_EX);
	    			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
						fsmInstance.setDesp(desp + ":Ignoring the return value will cause the program to ignore the status and circumstances of unexpected");
	    			
	    			list.add(fsmInstance);
	    		}
	    	}
	    	
	    	/**
	    	 * The code is like this:
	    	 * 1. malloc(5); or
	    	 * 2. if (malloc(5))
	    	 * {
	    	 * }
	    	 * Note: the second is the recommended format.
	    	 * then check if the method holds the MethodUnCKRetValuePostCondition feature or returns a PointDomain is in the second or not.
	    	 */
	    	if (!isInAssorInitStatement) {
	    		SimpleNode ifNode = (SimpleNode)funcNode.getFirstParentOfType(ASTSelectionStatement.class);
	    		
	    		if (ifNode == null || !ifNode.getImage().equals("if")) {
	    			FSMMachineInstance fsmInstance = fsm.creatInstance();
	    			fsmInstance.setRelatedASTNode(funcNode);
	    			fsmInstance.setResultString(funcNode.getImage());
	    			if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
	    				fsmInstance.setDesp(desp + DESP_EX);
	    			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
						fsmInstance.setDesp(desp + ":Ignoring the return value will cause the program to ignore the status and circumstances of unexpected");
	    			
	    			list.add(fsmInstance);
	    		}
	    	}
	    }
	    
		return list;
	}
}
