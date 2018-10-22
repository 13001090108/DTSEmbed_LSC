package softtest.rules.gcc.question;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTEqualityExpression;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTInitializer;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTRelationalExpression;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.ASTUnaryOperator;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.LocalScope;
import softtest.symboltable.c.MethodScope;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_Array;
import softtest.symboltable.c.Type.CType_BaseType;
import softtest.symboltable.c.Type.CType_Enum;
import softtest.symboltable.c.Type.CType_Pointer;
import softtest.symboltable.c.Type.CType_Unkown;



/** 
 *
 * @author chh
 */

public class CAEStateMachine {

	public static List<FSMMachineInstance> createCAEStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		Hashtable<VariableNameDeclaration, FSMMachineInstance> vfTable = new Hashtable<VariableNameDeclaration, FSMMachineInstance>();
		String xPath=".//SelectionStatement[@Image='if']/Expression[not(./AssignmentExpression/EqualityExpression)]//AssignmentExpression[./AssignmentOperator[@Operators='='] and ./AssignmentExpression] "+
		"|.//IterationStatement[@Image !='for']/Expression[not(./AssignmentExpression/EqualityExpression)]//AssignmentExpression[./AssignmentOperator[@Operators='='] and./AssignmentExpression]"+
		"|.//IterationStatement[@Image ='for' and count(*)=4]/Expression[2][not(./AssignmentExpression/EqualityExpression)]//AssignmentExpression[./AssignmentOperator[@Operators='='] and./AssignmentExpression]"+
		"|.//IterationStatement[@Image ='for' and count(*)<4]/Expression[1][not(./AssignmentExpression/EqualityExpression)]//AssignmentExpression[./AssignmentOperator[@Operators='='] and./AssignmentExpression]";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()){
			ASTAssignmentExpression assignmentExpression= (ASTAssignmentExpression)itr.next();
			SimpleNode parent=(SimpleNode)assignmentExpression.getFirstParentOfType(ASTEqualityExpression.class);
			if(parent == null)
				parent = (SimpleNode)assignmentExpression.getFirstParentOfType(ASTRelationalExpression.class);
			if(parent != null)
				continue;
			parent = (SimpleNode)assignmentExpression.getFirstParentOfType(ASTAssignmentExpression.class);
			if(parent != null){
				List<Node> unarys = new ArrayList<Node>(); 
				unarys = parent.findChildrenOfType(ASTUnaryExpression.class);
				if(unarys != null){
					boolean isoppo = false;
					for(Node unary : unarys){
						if(unary.jjtGetChild(0) instanceof ASTUnaryOperator){
							ASTUnaryOperator oper = (ASTUnaryOperator)unary.jjtGetChild(0);
							if(oper.getOperators().equals("!")){
								if(assignmentExpression.isSelOrAncestor((SimpleNode)unary)){
									isoppo = true;
									break;
								}
							}
						}
					}
				if(isoppo == true)
					continue;
			}
			}

			
			SimpleNode unode = (SimpleNode)assignmentExpression.jjtGetChild(0);
			if(unode == null)
				continue;
			if( unode instanceof ASTUnaryExpression){
				List<Node> idList  = new ArrayList<Node>();
				idList =unode.findChildrenOfType(ASTPrimaryExpression.class);
				for(Node pnode : idList){
					ASTPrimaryExpression snode = (ASTPrimaryExpression)pnode;
					if (snode.getVariableNameDeclaration() == null ) {
			    		continue;
			    	}
			    	VariableNameDeclaration variable = (VariableNameDeclaration)snode.getVariableNameDeclaration();
			    	CType type = variable.getType();
			    
			    	if ( type instanceof CType_Unkown) {
			    		continue;
			    	}
			    	if(!(type instanceof CType_BaseType || type instanceof CType_Pointer || type instanceof CType_Enum || type instanceof CType_Array)){
			    		continue;	    		
			    	}
			    	// 数组类型只考虑数组成员是简单类型的变量
			    	if (type instanceof CType_Array && !(((CType_Array)type).getOriginaltype() instanceof CType_BaseType)) {
			    		continue;
			    	}
			    	//不考虑全局变量
			    	if(!(variable.getScope() instanceof LocalScope || variable.getScope() instanceof MethodScope)){
			    		continue;
			    	}

			    	if(checkInitBefore(variable,snode))
			    		addFSM(list,assignmentExpression,fsm);
				}
			}
		}
		return list;  
	}
	
	
	/**通过variable在得到变量的出现*/
    private static NameOccurrence getOcc(VariableNameDeclaration variable,SimpleNode node){  	
    	Map<VariableNameDeclaration, ArrayList<NameOccurrence>> variableNames = null;
    	ArrayList<NameOccurrence> occs = null;
    	variableNames = variable.getScope().getVariableDeclarations();
    	occs = variableNames.get(variable);
    	for(NameOccurrence occ : occs){
    		if(occ.getLocation().equals(node))
    			return occ;
    	}
    	return null; 
    }
	
    /**检测状态机相关变量是否被初始化*/
	public static boolean checkInitBefore(VariableNameDeclaration var,SimpleNode node) {

		NameOccurrence occ = getOcc(var,node);
		List<NameOccurrence> defineList = null;
		defineList = occ.getUndef_def();
		if(var.isParam()) 
			return true;
		if(defineList == null)
			return false;
		if(isinit(defineList))
			return true;
		else return false;
		
	}
	
	public static boolean isinit(List<NameOccurrence> list){
		for(NameOccurrence o : list){
			if(o.getLocation() instanceof ASTPrimaryExpression)
				return true;
			if(o.getLocation() instanceof ASTDirectDeclarator){
				SimpleNode snode = o.getLocation();
				SimpleNode dec = (SimpleNode)snode.getFirstParentOfType(ASTInitDeclarator.class);
				if(dec == null)
					return false;
				if(dec.findChildrenOfType(ASTInitializer.class) == null || dec.findChildrenOfType(ASTInitializer.class).size() == 0)
					return false;
				else return true;
			}
		}
		return false;
	}
	

	
	

	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(" ConfuseAssignmentEquallity: \"==\" may be misused \"by confusion with \"==\".When the code is complex，error like this is usually difficult to check out.So it's better to do assignement before judgement other than in judgement");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("第"+node.getBeginLine()+"行：= = 与 =运算符的混淆: 在if或while语句中进行条件判定时，有时候会把\"==\"误写成\"=\"。当代码很复杂时，这种错误一般很难检查出来。建议赋值在判断前完成，不要写在判定条件中");
						}	
		list.add(fsminstance);
	
	}
}

		
		


