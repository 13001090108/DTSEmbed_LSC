package softtest.rules.gcc.safety;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.MethodNameDeclaration;

/**
 * Create state machine to check some password functions.
 * @author liuyan
 *
 */
public class PwdStateMachine {
	private final static String HARD_CODE = "该方法第4个实参存在问题,使用了硬编码密码：硬编码会降低系统安全性，并且难以补救。";
	private final static String PLAINTEXT_CODE = "该方法第4个实参存在问题,使用了明文密码：使用配置文件、注册表存储密码或者常量字符串作为密码会导致系统安全性降低。";
	private final static String EMPTYP_CODE = "该方法第4个实参存在问题,使用了空密码:使用空密码是不安全的。";
	private final static String FILE_RECORD = "密码存储在变量中，导致系统安全性降低，这是不安全的。";
	private final static String LINUX_VERB_RECORD = "使用密码函数getgrent(),密码存储在文件或变量中，可能将组文件的密码泄露，导致系统的安全性降低，这是不安全的。";
	
	public static List<FSMMachineInstance> createPwdStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xPath=".//UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true'] " +
				"|.//Expression/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		String isNULL = null;
		
		for (SimpleNode funcNode : evaluationResults) {
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(funcNode);	
			if(methodDecl == null ){
				continue;
			}
			//Linux C下密码函数检查
			if(methodDecl.getImage().equals("getgrent")){
				SimpleNode getParent = (SimpleNode) funcNode.jjtGetParent().jjtGetParent().jjtGetParent().jjtGetParent();
				if(getParent != null && getParent instanceof ASTAssignmentExpression){
					SimpleNode oper = (SimpleNode) getParent.jjtGetChild(1);
					if(oper.getOperators().equals("=")){//使用getgrent并返回给一个变量加入状态机
						FSMMachineInstance fsmInstance = fsm.creatInstance();
						fsmInstance.setRelatedASTNode(funcNode);
						fsmInstance.setResultString(funcNode.getImage());
						fsmInstance.setDesp(LINUX_VERB_RECORD);
						list.add(fsmInstance);
					}
				}
			}
			
			//WIN下密码函数检查
			//密码存储在文件中
			if(!methodDecl.getImage().equals("getgrent")){
				if(methodDecl.getImage().equals("mysql_real_connect")){
					SimpleNode getParents = (SimpleNode) funcNode.jjtGetParent().jjtGetParent().jjtGetParent().jjtGetParent();
					if(getParents != null && getParents instanceof ASTAssignmentExpression){
						SimpleNode opr = (SimpleNode) getParents.jjtGetChild(1);
						if(opr.getOperators().equals("=")){//创建密码存储在文件中的状态机
							FSMMachineInstance fsmInstance = fsm.creatInstance();
							fsmInstance.setRelatedASTNode(funcNode);
							fsmInstance.setResultString(funcNode.getImage());
							fsmInstance.setDesp(FILE_RECORD);
							list.add(fsmInstance);
						}
					}
				}

			}
			
			String argXpath ="../ArgumentExpressionList/AssignmentExpression[4]/UnaryExpression/PostfixExpression/PrimaryExpression";
			List<SimpleNode> argNodeList = StateMachineUtils.getEvaluationResults(funcNode, argXpath);
			if (argNodeList == null || argNodeList.size() == 0) {
				continue;
			}
			//首先判断出函数是密码验证函数
			if(methodDecl.getImage().equals("mysql_real_connect") ){
				if(argNodeList != null || argNodeList.size() != 0){
					SimpleNode argNode = (SimpleNode)argNodeList.get(0);
					if(argNode instanceof ASTPrimaryExpression){
						if(argNode.jjtGetNumChildren() == 0){//明文密码
							FSMMachineInstance fsmInstance = fsm.creatInstance();
							fsmInstance.setRelatedASTNode(funcNode);
							fsmInstance.setResultString(funcNode.getImage());
							fsmInstance.setDesp(PLAINTEXT_CODE);
							list.add(fsmInstance);
						}else if(argNode.jjtGetNumChildren() == 1){	//硬编码或者空密码
							if( argNode.jjtGetChild(0) instanceof ASTConstant){//硬编码
								FSMMachineInstance fsmInstance = fsm.creatInstance();
								fsmInstance.setRelatedASTNode(funcNode);
								fsmInstance.setResultString(funcNode.getImage());
								fsmInstance.setDesp(HARD_CODE);
								list.add(fsmInstance);
							}
							//判断密码为NULL
							else if( argNode.jjtGetNumChildren() == 1 && argNode.jjtGetChild(0) instanceof ASTExpression){
								SimpleNode temp = (SimpleNode) argNode.jjtGetChild(0);
								for( int k = 0; k < 30; k++ ){
									isNULL = temp.getImage();
									if( isNULL.equals("void") ){
										break;
									}else{
										temp = (SimpleNode) temp.jjtGetChild(0);
									}
								}
								if(isNULL.equals("void")){
									FSMMachineInstance fsmInstance = fsm.creatInstance();
									fsmInstance.setRelatedASTNode(funcNode);
									fsmInstance.setResultString(funcNode.getImage());
									fsmInstance.setDesp(EMPTYP_CODE);
									list.add(fsmInstance);
								}
							}
						}
					}
				}
				
			}
		}
		return list;
	}
}

