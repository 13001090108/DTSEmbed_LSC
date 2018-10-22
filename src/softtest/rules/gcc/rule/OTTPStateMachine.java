package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTDeclarator;
import softtest.ast.c.ASTInitializer;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.ASTUnaryOperator;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_AbstPointer;


/** 
 * @author xiangwentao
 * 使用其它类型变量给指针赋值
 * OtherTypeToPointer
 */
public class OTTPStateMachine {

	public static List<FSMMachineInstance> createOTTPStateMachines(SimpleNode node,FSMMachine fsm){
		
		String AssignXpath = ".//ExpressionStatement//AssignmentExpression[./AssignmentOperator[@Operators = '=']]";
		String InitXpath = ".//Declaration//InitDeclarator[./Declarator[not(.//DeclaratorSuffixes) and not(.//ConstantExpression)] and ./Initializer[ not(.//CastExpression)] ]";
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		
		List<SimpleNode> assignResults = StateMachineUtils.getEvaluationResults(node, AssignXpath);
		for(SimpleNode snode : assignResults){
			ASTUnaryExpression UnaryExp = (ASTUnaryExpression) snode.jjtGetChild(0);
			ASTAssignmentExpression AssignmentExp;
			if(snode.jjtGetChild(2) instanceof ASTAssignmentExpression){
				AssignmentExp = (ASTAssignmentExpression) snode.jjtGetChild(2);
			}else{
				return list;
			}
			if(UnaryExp.getType() == null || AssignmentExp.getType() == null)
				continue;
			if(UnaryExp.getType() instanceof CType_AbstPointer){
				if(!(AssignmentExp.getType() instanceof CType_AbstPointer) && !(AssignmentExp.getType().getNormalType() instanceof CType_AbstPointer )){
					if(AssignmentExp.getImage().equals("0"))
						continue;
					addFSM(list,snode,fsm,AssignmentExp.getType());
				}
			}
		}
		
		List<SimpleNode> initResults = StateMachineUtils.getEvaluationResults(node, InitXpath);
		for(SimpleNode snode : initResults){
			ASTDeclarator Declarator = (ASTDeclarator) snode.jjtGetChild(0);
			ASTUnaryExpression UnaryExp = (ASTUnaryExpression) ((ASTInitializer) snode.jjtGetChild(1)).getFirstChildOfType(ASTUnaryExpression.class);;
			if(UnaryExp == null)
				continue;
			ASTUnaryOperator Operator = new ASTUnaryOperator(0);
			if(Declarator.getType() == null)
				continue;
			if(Declarator.getType() instanceof CType_AbstPointer){
				
				if(UnaryExp.jjtGetNumChildren() != 1){
					Operator = (ASTUnaryOperator)UnaryExp.jjtGetChild(0);
					if(Operator.getOperators() == "&")
						continue;
				}
//<<<<<<< OTTPStateMachine.java
				if(UnaryExp.jjtGetParent() instanceof ASTAssignmentExpression){
					ASTAssignmentExpression ass = (ASTAssignmentExpression)UnaryExp.jjtGetParent();
					if(ass.getType() ==null)
						continue;
					if(!(ass.getType() instanceof CType_AbstPointer)){
						if(!(ass.getType().getNormalType() instanceof CType_AbstPointer)){
							if(ass.getImage().equals("0"))
								continue;
							addFSM(list,snode,fsm,ass.getType());
						}
//=======
				ASTAssignmentExpression ass1 = (ASTAssignmentExpression)(UnaryExp.getFirstParentOfType(ASTAssignmentExpression.class));
				if(ass1 == null)
					continue;
				if(ass1.getType() ==null)
					continue;
				if(!(ass1.getType() instanceof CType_AbstPointer)){
					if(!(ass1.getType().getNormalType() instanceof CType_AbstPointer)){
						if(ass1.getImage().equals("0"))
							continue;
						addFSM(list,snode,fsm,ass1.getType());
//>>>>>>> 1.2.2.2
					}
				}
			}			
		}
			}
		}
		return list;		
	}
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm, CType type) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("OtherTypeToPointer: When assign other type ("+type.toString()+") to pointer it is advised to use the address operation,otherwise it is dangerous. ");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("使用其它类型变量给指针赋值: 用其它类型("+type.toString()+")类型变量给指针赋值时，要用取地址运算，否则是很危险的。");
			}	
		
		list.add(fsminstance);
	}
}
